## Worker report

The module `Sheaf.AlgebraicGeometry.NormalSubgroupCharacterInversion` states
`AlgebraicGeometry.normalSubgroup_character_inverse_power_occurs`, with its sole proof
`by sorry`. It introduces no definitions, copies no notion, and changes only the item's
`lean` field. Source: Milne, Algebraic Groups (2017), Lemma 5.16, printed pp.102–103;
the PDF was read with pdftotext, including both the dense-points case and Frobenius reduction.
The declaration docstring carries all five proof steps of the DAG, including its explicit
base-changed representation formulation of Milne's Frobenius argument.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The given group scheme is `G : Over (Spec (.of k))` with `[GrpObj G]`.
  Affineness is `[IsAffine G.left]`; finite type is the recorded conjunction represented by
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- The subgroup scheme is `N : Over (Spec (.of k))` with `[GrpObj N]`, inclusion `i : N ⟶ G`,
  `[IsClosedSubgroupScheme i]` and `[IsNormalSubgroupScheme i]`. Both are the existing
  pointwise-on-all-algebras classes. No extra affineness, finite-type or smoothness
  hypothesis on N is needed or added.
- A character is `(χ : N ⟶ StandardGroupSchemes.multiplicative k) [IsMonHom χ]`.
- The occurrence assumption `hχ` existentially quantifies a dimension `n : ℕ`, an actual
  scheme morphism `ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n))`,
  its `IsMonHom` proof, and `U : Submodule k (ULift.{u} (Fin n) → k)`.
  Thus V is the coordinate vector space k^n after the basis choice expressly allowed
  by the node. Every finite-dimensional vector space has such a basis; no dimension,
  basis-invariance or semisimplicity assumption is imposed.
- The occurrence subspace is nonzero exactly by `U ≠ ⊥`.
- For every test algebra `A : Type u` with `[CommRing A] [Algebra k A]`, `h : points N A`
  is an A-point, namely Spec A → N over Spec k. Composition `h ≫ i ≫ ρ` gives its
  action matrix via the existing `GeneralLinearGroup.homMulEquiv`.
- The scalar extension U tensor A, inside V tensor A, is the `Submodule.span A` of the
  image of U under coordinatewise `algebraMap k A`. Because k is a field this is
  exactly the image of the injective scalar extension of the inclusion U → V;
  coordinates identify V tensor A with A^n. The displayed equation is required for
  every `v` in this entire span, not just for k-points or basis vectors.
- `Matrix.toLin' (...) v` is the actual A-linear action on A^n. Its scalar is
  `(Spec.preimage (h ≫ χ).left).hom (LaurentPolynomial.T 1)`, i.e. χ_A(h).
  `Spec.preimage` is the existing full-faithful affine Spec inverse, so this is
  evaluation of the character's coordinate map, not a freely supplied function.
- The conclusion gives `∃ (m : ℕ), 0 < m ∧ ...`. Positive natural m and positive integer
  m describe precisely the same permitted exponents. It existentially supplies a new
  dimension, rational G-representation and subspace T, with `T ≠ ⊥`.
- The conclusion repeats the same all-algebra/all-vector scalar equation, with
  `LaurentPolynomial.T (-(m : ℤ))`. This is t^(-m). A coordinate ring map sends it
  to χ_A(h)^(-m), since the image of t is a unit, including over nonreduced and zero
  algebras. No inversion operation on a general ring element is assumed.
- Nonreduced G and N and positive characteristic are retained: there is no smoothness,
  reducedness, characteristic-zero, connectedness or field-test restriction. In dimension
  zero the upstream GL construction uses the empty matrix coordinate algebra, giving
  Spec k; the nonzero occurrence condition then correctly cannot hold.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the algebraic-closure dependency's
  record explicitly names this predicate for the phrase algebraically closed.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, used through Over and Spec;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine` (def-pc-scheme).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, through the group-scheme
  dependency and its upstream Defs module.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`, with their full class signatures and docstrings read.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: the recorded GL dependency module,
  reusing its upstream `AlgebraicGeometry.GeneralLinearGroup` and
  `AlgebraicGeometry.GeneralLinearGroup.homMulEquiv`; their definitions/docstrings
  were read in `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`:
  `GeneralLinearGroup.RationalHom` (actual morphism G → GL), read with its point-map API.
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring`: `points`.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional` is `Module.Finite`;
  finite coordinate spaces are instances via `FiniteDimensional.Basic`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative` and its canonical
  Laurent Hopf `GrpObj` instance (def-sc-gm-ga).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage` for coordinate maps;
  the Laurent monomials are the existing `LaurentPolynomial.T`.

Proof imports: `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusSmoothImage`
(`affine_group_frobenius_smooth_image`, its full signature and docstring were read) and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (`pullback`). The other two
proof-only nodes `lem-sfb-smooth-group-rational-point-subspace-test` and
`lem-sfb-character-eigenspaces-independent` have neither Lean records nor Mathlib matches
in the read clone, so there are no recorded proof modules to import for them. They are
not needed to type this statement. The subgroup and GL proof dependencies are already
public statement imports. There are no missing statement notions and no new nodes.

Edge cases checked before writing and again against the final statement: n=0 has only
zero subspaces, so cannot witness occurrence; trivial character permits m=1 and a trivial
line; the trivial subgroup is allowed; disconnected groups are allowed; positive
characteristic and nonreduced groups/subgroups retain algebra-valued points; arbitrary
nonreduced test algebras are included; the zero algebra is included and its scalar equation
is automatically the zero equation. G cannot be an empty group scheme over a field because
its group structure has an identity section. All universes are explicit. As in the recorded
group-scheme API, k, schemes, finite coordinate spaces and test algebras share u. This loses
no finite-dimensional V, even if originally presented in a larger type universe: its finite
basis transports it to the coordinate space. Universal affine coordinate identities in
universe u determine the identities after every larger-algebra base change as well.

Searches performed (2026-10-24):

- msearch LeanFinder: “An occurring character of a normal subgroup scheme has an inverse
  positive power occurring in a finite dimensional rational representation”. Eight hits,
  including FDRep.char_dual and character orthogonality, concern trace characters of
  abstract-group representations; none state this scheme-theoretic result.
- msearch LeanSearch: “A character occurring in a rational representation of an affine
  algebraic group has a negative multiple occurring when its subgroup is normal”. Eight
  hits concern abstract-group invariants, trace conjugation and CharacterModule; no match.
- msearch Loogle: `Representation.character, FDRep.char_dual` gave no hits; the valid quoted
  query `"Representation", "character"` gave `Representation.character` and
  `Representation.isIntegral_character`, both trace-character declarations, not a match.
- msearch grep: `character.*(inv|neg)|char_dual` in RepresentationTheory found five lines
  in Mathlib/RepresentationTheory/Character.lean, all on the abstract-group trace dual.
- rg in WeilConjectures and Sheaf for rationalRepresentation/RationalRepresentation,
  characterOccurs/CharacterOccurs, inverse/negative character and character_inversion;
  no theorem matching this result. `rg -n lem-sfb-normal-subgroup-character-inversion
  lean/WeilConjectures` found none. Exact new declaration name searches also found none.
- Concept search found the already landed
  `Sheaf.AlgebraicGeometry.ChevalleyCharacterCancellation` declaration's `hc` hypothesis.
  Its occurrence and inverse-power formulas are exactly reused here. This is a hypothesis
  assumed by that lemma, not a theorem already proving the present result, so existing:true
  would be incorrect. Its use of upstream RationalHom and coordinate GL also confirms
  no new definition is needed. The NaturalRepresentation/comodule dictionary was read;
  its natural-action encoding is equivalent but unnecessary because the node expressly
  uses scheme homomorphisms into GL after a basis choice.

No statement correction, dependency repair, or STATEMENT-DISPUTED fault was found.

## Second reading by NX

Independent second reading (maintainer reviewer, replacing the author's self-check of the
delivered report; the Lean module and the node record are unchanged).

Node statement as a list, with the Lean rendering and verdict:

1. k algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]` (def-weil-field,
   def-weil-algebraic-closure). Correct.
2. G affine group scheme of finite type over k: `G : Over (Spec (.of k))`, `[GrpObj G]`,
   `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`. Correct; same
   encoding as the landed `chevalley_character_cancellation`.
3. N ⊆ G closed normal subgroup scheme: `N`, `[GrpObj N]`, `i : N ⟶ G`,
   `[IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i]`. Read in
   WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: both extend `IsSubgroupScheme`
   (IsMonHom + injective on all R-points), closed = closed immersion, normal = image of
   N(R) normal in G(R) for every k-algebra R. Exactly def-sc-group-scheme-subgroup; no extra
   hypothesis on N (affineness/finite type follow from closedness).
4. Character χ : N → G_m: `χ : N ⟶ StandardGroupSchemes.multiplicative k` with `[IsMonHom χ]`;
   `multiplicative k = Spec k[t,t⁻¹]` with the Laurent Hopf law t ↦ t⊗t (def-sc-gm-ga).
   χ_A(n) = image of `T 1` under the coordinate map `Spec.preimage (h ≫ χ).left`. Correct.
5. Rational representation G → GL(V), V finite-dimensional, after a basis choice:
   `ρ : GeneralLinearGroup.RationalHom G (ULift (Fin n))` (= `G ⟶ 𝔾𝕃(n;k)`) with `IsMonHom ρ`;
   action on A-points via `homMulEquiv` (≃*, matrices ψ(x_ij)) and `Matrix.toLin'`. Correct;
   n = 0 is allowed (GL_0 = Spec k).
6. "χ occurs": ∃ n ρ, U ≠ ⊥ with, for every `A : Type u` k-algebra, every `h : points N A`
   (= Spec A ⟶ N over Spec k) and every v in the A-span of U (= U ⊗_k A ⊆ A^n, k a field),
   ρ(i h) v = χ_A(h) • v. Correct.
7. Conclusion: ∃ m : ℕ, 0 < m, a new (n, ρ, T ≠ ⊥) with the same all-algebra, all-vector
   equation for `T (-(m:ℤ))`, i.e. χ_A(h)^{-m} (image of a unit, no division in A needed).
   Quantifier order (∃ m, ∃ W, ∃ T, ∀ A ∀ n) as in the node. Neither weaker nor stronger.

The hypothesis and conclusion formulas are byte-identical to the `hc` hypothesis of the
landed `Sheaf.AlgebraicGeometry.ChevalleyCharacterCancellation` (with H renamed N), so the
consumer route can apply this theorem directly.

Edge cases: n = 0 (no nonzero U, hypothesis false, consistent); zero algebra (equation
trivial); nonreduced G, N, A and characteristic p retained (no smoothness/reducedness/char
assumption); disconnected G allowed; trivial N and trivial χ allowed (m = 1).
Universes: k, schemes, test algebras share u, as in the recorded group-scheme API; the scalar
identities are coordinate-ring identities tested on the universal point, so no case is lost.

Records: the node copy differs from the live node only in the `lean` field; `lean.statement`
occurs verbatim in the module. Module: no definitions, single theorem `by sorry`, source place
and `(blueprint: ...)` in module and declaration docstrings, all five proof steps in the
declaration docstring. Proof-only import `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusSmoothImage`
exists in the live tree. No pro-étale content.

Searches: rg for character inversion / inverse power / occurring character in lean/Sheaf and
lean/WeilConjectures found only the Chevalley `hc` hypothesis (an assumption, not a theorem),
so existing:true is not available; Mathlib's `Representation.character`/`FDRep.char_dual` are
trace characters of abstract groups. No mismatch found.
