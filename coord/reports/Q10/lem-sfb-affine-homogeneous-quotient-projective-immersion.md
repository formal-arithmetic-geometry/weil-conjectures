## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.AffineHomogeneousQuotientProjectiveImmersion`
states `AlgebraicGeometry.exists_projectiveSpace_immersion_of_affine_homogeneous_quotient`.
There is one theorem, with proof `sorry`, and no new definitions. The node is unchanged
except for its `lean` record. Its proof is copied as a six-step natural-language plan
in the theorem docstring.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, printed p.143,
Proposition 7.17, Theorem 7.18 and its proof, and Example 7.19. The proof applies
Chevalley's scheme-theoretic line stabilizer and Proposition 7.17 to projective
space. Our node concerns a given represented quotient, so the existing six-step
DAG proof also identifies that quotient with this orbit by fpqc descent.

Hypothesis-by-hypothesis and conclusion-by-conclusion correspondence:

- The field is `{k : Type u} [Field k]`, with `u` arbitrary.
- The two group schemes are `G H : Over (Spec (.of k))` with `[GrpObj G]` and
  `[GrpObj H]`. This uses the group-scheme dependency's recorded interface.
- Affineness of G is `[IsAffine G.left]`; finite type is
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`; smoothness is `[Smooth G.hom]`.
- The closed subgroup is `i : H ⟶ G` with `[IsClosedSubgroupScheme i]`, the
  recorded upstream definition. This supplies the homomorphism, subgroup, and
  closed-immersion conditions. No separate finite-type or affine assumption on H
  was added: these follow from its closed inclusion into G.
- The separated finite-type k-scheme is `Y : Over (Spec (.of k))` with
  `[IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]`.
  Y is a scheme, without a group structure.
- The quotient map is `q : G ⟶ Y`; the slice-category type requires it to be over k.
- Faithful flatness is exactly `[Flat q.left] [Surjective q.left]`.
- Finite presentation is exactly `[LocallyOfFinitePresentation q.left]`,
  `[QuasiCompact q.left]`, and `[QuasiSeparated q.left]`.
- The final hypothesis is
  `IsPullback (fst G H) (fst G H * (snd G H ≫ i)) q q`.
  In the Cartesian monoidal category of k-schemes, `fst G H` is `(g,h) ↦ g` and
  `snd G H ≫ i` is `(g,h) ↦ i(h)`. Multiplication of these morphisms is
  `lift (fst G H) (snd G H ≫ i) ≫ MonObj.mul`, hence `(g,h) ↦ g i(h)`.
  `IsPullback` extends `CommSq`, so its commutativity states right H-invariance
  of q. Its limit condition states precisely that this cone is a fibre product
  G ×_Y G. Equivalently, the specified canonical map `(g,h) ↦ (g,gh)` is an
  isomorphism to G ×_Y G. It does not assert merely the existence of an arbitrary
  isomorphism between the two schemes. The slice product is the scheme fibre
  product over Spec k (`Over.tensorObj_left`); pullbacks in the slice are
  created by its forgetful functor. Thus this is the node's scheme-level condition.
- `∃ (N : ℕ)` supplies N ≥ 0 without an extra redundant inequality.
- The target of j is
  `ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k))`.
  ProjectiveSpace indexes homogeneous coordinates, so N+1 coordinates are exactly
  classical projective N-space. ULift puts this finite index type in `Type u`
  without restricting the field or scheme universe.
- `IsImmersion j` means exactly a closed immersion followed by an open immersion,
  by `AlgebraicGeometry.isImmersion_iff_exists` in Mathlib's Immersion module.
- `j ≫ (... ↘ Spec (.of k)) = Y.hom` requires the immersion to be over k.
- There is no assumption of normality or smoothness on H, of connectedness or
  reductivity on G, or of perfection on k. The connectedness definition is only
  mentioned by the node to clarify what is *not* assumed; no connectedness
  hypothesis or unused connectedness import is introduced.

Dependency declarations read and used:

- `Field` from `Mathlib.Algebra.Field.Defs` (via the algebraic-geometry imports).
- `CategoryTheory.GrpObj` from `Mathlib.CategoryTheory.Monoidal.Grp`, and
  `AlgebraicGeometry.IsClosedSubgroupScheme` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.Scheme` and its morphisms, from `Mathlib.AlgebraicGeometry.Scheme`;
  `IsAffine` from the existing scheme-affineness API.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact` from the recorded
  FiniteType/QuasiCompact Mathlib modules, and `Smooth` from Morphisms.Smooth.
- `AlgebraicGeometry.IsSeparated` through the recorded Morphisms.Proper module;
  `Flat`, `LocallyOfFinitePresentation`, and `QuasiSeparated` from their recorded
  Mathlib morphism modules; `Surjective` is Mathlib's scheme-morphism property.
- `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd` underlie
  the Cartesian products and `CategoryTheory.IsPullback`. The latter is the
  existing universal-property predicate, not a new definition of quotient.
- `AlgebraicGeometry.IsClosedImmersion` and `IsOpenImmersion` underlie
  `AlgebraicGeometry.IsImmersion`, through its read closed/open factorization theorem.
- `AlgebraicGeometry.ProjectiveSpace` and its canonical structure map from the
  recorded `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` module.

Proof dependency imports: the projective-space functor-of-points module is imported
non-publicly, as is `Mathlib.AlgebraicGeometry.Sites.Fpqc` for the fppf/fpqc and
representable-descent leaves. ProjectiveSpace already supplies its properness
instance. Yoneda and fibre products are already imported through the public
interfaces. The Chevalley scheme-line stabilizer and arbitrary-field rational-orbit
nodes have no recorded Lean declarations at this snapshot, so no nonexistent
modules are imported. They are proof prerequisites, not notions needed to type
this statement. Their six-step proof roles remain in the docstring and DAG.

Edge cases checked against the signature and source:

- H = G: the quotient is Spec k, and N = 0 is permitted. This includes G = 1.
- H trivial and positive-dimensional affine G: the result is an immersion, with
  no closedness or properness conclusion imposed.
- H = μ_p in G_m in characteristic p, including over an imperfect field:
  nonreduced H and the Frobenius quotient are admitted; no smoothness or normality
  condition on H occurs in the signature.
- Disconnected smooth affine G is allowed; no ConnectedSpace instance is required.
- Empty Y cannot satisfy surjectivity from a group scheme over a field: the unit
  supplies a rational point of G. Thus no exceptional empty case was excluded.
- Arbitrary characteristics and arbitrary universe u are covered. N = 0 uses
  one homogeneous coordinate; a zero-coordinate empty projective space was not
  accidentally substituted for it.

Searches made before writing:

- `msearch.py ... leanfinder "A smooth affine algebraic group quotient by a closed
  subgroup admits an immersion into projective space over an arbitrary field"`:
  eight hits including Proj, the projective-spectrum open charts, quotient-ring
  closed immersions, and quasi-affine immersions. None is a homogeneous-quotient
  projective-immersion theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsImmersion,
  AlgebraicGeometry.ProjectiveSpace"`: no hits; Loogle does not know the
  project's ProjectiveSpace declaration. Its local source was read directly.
- `msearch.py ... leansearch "Every homogeneous quotient of a smooth affine
  algebraic group by a closed subgroup is quasi projective"`: eight hits on
  topological group quotients and affine quasi-compactness, none matching.
- `msearch.py ... grep
  "homogeneous.*quasi.?projective|quotient.*quasi.?projective|quasi.?projective.*quotient"`:
  zero Mathlib hits.
- `rg -n` with the same conceptual pattern in `lean/WeilConjectures` and
  `lean/Sheaf`, plus the exact node id and the proposed declaration name:
  no existing matching theorem. One unrelated comment concerned a modification
  of a log-regular quotient.
- Existing group-scheme quotient declarations in `lean/Sheaf` were inspected.
  The homogeneous-orbit statements require an algebraically closed field and
  connected G, so they cannot replace this arbitrary-field statement. The
  special reductive quotient predicates impose extra group/geometric hypotheses.
  The present theorem therefore uses the recorded primitive notions directly.

Validation: `scompile.py Q10 lem-sfb-affine-homogeneous-quotient-projective-immersion
<module>` compiled the sandbox module and its intended library module cleanly on
2026-10-24 (2.1 s and 3.0 s respectively). No node fault or statement correction
was necessary.

## Second reading by Q10

I reopened the node and the complete module for a separate second pass. The
check matches the arbitrary field, both group objects, affineness, smoothness and
finite type of G, the closed subgroup inclusion, separated finite-type Y, the
five quotient-map morphism properties, and the canonical right-H kernel pair
with their binders above. In particular hq includes the invariance equality and
requires a Cartesian square with the *specified* two arrows. The conclusion
has N+1 coordinates and the explicit k-structure equation; `IsImmersion` gives
the required closed/open factorization. No extra connectedness, algebraic
closure, reductivity, or smoothness of H entered. No mismatch was found and no
statement change was made. This is the same worker's separate reading: the
dispatcher explicitly prohibits starting other agents; the maintainer's review
will be independent.
