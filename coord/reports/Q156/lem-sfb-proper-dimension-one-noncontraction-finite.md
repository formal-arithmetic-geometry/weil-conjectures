## Worker report

The module `Sheaf.AlgebraicGeometry.ProperDimensionOneNoncontractionFinite` states
`AlgebraicGeometry.isFinite_of_proper_dim_le_one_noncontraction`, with proof `sorry`.
No definitions, helper nodes, dependency repairs, or statement corrections are needed.
The source read is `literature/stacks-project/curves.tex`, lemma-finite, lines 105–135
(Stacks Tag 0CCL). Its three numbered hypotheses and conclusion agree with the DAG.
The theorem docstring carries all seven steps of the accepted proof and their node ids.

Hypothesis and conclusion correspondence:

- The field is `{k : Type u} [Field k]`.
- The schemes are `{X Y : Scheme.{u}}`, with
  `[X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]` giving their structure morphisms.
- The k-morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`.
  The latter is Mathlib's assertion that `f ≫ Y ↘ Spec (.of k) = X ↘ Spec (.of k)`.
- Separatedness of Y over k is `[IsSeparated (Y ↘ Spec (.of k))]`.
- Properness of X over k is `[IsProper (X ↘ Spec (.of k))]`.
- The dimension bound is `h_dim : topologicalKrullDim X ≤ 1`, using precisely the
  topological Krull dimension, valued in `WithBot ℕ∞`.
- Each component is quantified as `∀ Z : Set X, Z ∈ irreducibleComponents X →`.
  The restriction to dimension-one components is `topologicalKrullDim Z = 1 →`,
  where Z has the subspace topology. The image condition is `(f '' Z).Nontrivial`,
  i.e. the set-theoretic image contains two unequal points, exactly “at least two points.”
- The sole conclusion is `IsFinite f`.

Dependency interfaces read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-scheme-over-base`: `Scheme.Over` and `Scheme.Hom.IsOver` in
  `Mathlib.AlgebraicGeometry.Over`, including `Scheme.Hom.isOver_iff`.
- `def-weil-proper-morphism`: `IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; also `IsSeparated` and `UniversallyClosed`
  in their Mathlib morphism modules. Properness uses locally finite type and universally
  closed (which implies quasi-compact), exactly the recorded dependency's finite-type meaning.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, defined as `Order.krullDim (IrreducibleCloseds T)`.
- `def-weil-irreducible-components`: `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`, defined as maximal nonempty irreducible subsets.
- `def-weil-finite-integral-morphism`: `IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, the affine-preimage/finite-ring-map predicate.

All statement dependency interfaces are exposed using public imports. Stated proof
prerequisites are imported privately from their Mathlib modules: `IsProper.of_comp`,
`LocallyOfFiniteType`, `Algebra.FiniteType.isNoetherianRing`,
`PrimeSpectrum.instNoetherianSpace`,
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`, the scheme sober/T0
instances and `IsGenericPoint.eq`,
`exists_isFinite_morphismRestrict_of_finite_preimage_singleton`,
`LocallyOfFiniteType.jacobsonSpace` and `JacobsonSpace.closure_inter_closedPoints`,
`IsAffineHom`/the affine-cover criterion, and `IsFinite.iff_isProper_and_isAffineHom`.
There are no omitted recorded project-module imports: these prerequisites are Mathlib matches.

Edge cases checked before writing:

- Empty X has dimension bottom, satisfies the bound and has no irreducible components.
  Its noncontraction hypothesis is vacuous and its map is finite. No nonemptiness is imposed.
- Dimension-zero X also has no dimension-one components, so the condition is vacuous;
  the conclusion is the correct finite-map case for a proper zero-dimensional source.
- A constant map from a proper irreducible curve fails precisely the noncontraction
  hypothesis; a singleton image is not `Set.Nontrivial`.
- Reducible X can contain both zero-dimensional and one-dimensional components.
  Only the latter are constrained, exactly as in the node. Reducedness, irreducibility,
  smoothness, and connectedness are not assumed.
- Y can be empty (then existence of f forces X empty) or non-Noetherian; no finite-type
  hypothesis on Y is added. Any field characteristic is allowed.
- The universe `u` is explicitly declared and all binders are explicit; `autoImplicit false`
  is enabled. No test-object universe or extra universe equality is introduced.

Searches performed with the prescribed wrapper:

- LeanFinder: “A morphism from a proper scheme of dimension at most one to a separated
  scheme over a field is finite if every dimension one irreducible component has at
  least two image points”. Eight hits: IsFinite, finite-of-composite, proper/affine
  criteria, etc.; no dimension/noncontraction criterion.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProper`. Nine hits, including
  the proper/affine and proper/locally-quasi-finite criteria and finite-neighbourhood lemma;
  none states this item.
- grep of Mathlib AlgebraicGeometry: `nonconstant|non_constant|contract.*component`.
  Zero hits.
- LeanSearch: “A morphism from a proper scheme of dimension at most one to a separated
  scheme over a field is finite if no irreducible curve component is contracted”.
  Eight hits consisting of the finite-morphism definition and general proper/finite facts;
  none states this criterion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `0CCL|noncontraction|noncontract|dimension_one.*[Ff]inite|isFinite.*[Dd]im|[Ff]inite.*[Nn]onconstant`:
  related zero-dimensional finite results, an affine-space normalization result,
  and an unrelated relative-curve contraction statement; no exact existing declaration.
- `rg` of `lean/WeilConjectures` for the item id: no hits.
- Exact declaration-name search in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no hits.

The historical example `Sheaf.CategoryTheory.CompactObject` has been withdrawn;
its node now points to `WeilConjectures.CategoryTheory.CompactObject`. This delivery uses
current module mode, public statement imports and `@[expose] public section` as prescribed.
No node faults or STATEMENT-DISPUTED issues found.

Validation: `scompile.py Q156 lem-sfb-proper-dimension-one-noncontraction-finite
<module path>` succeeded in both sandbox and library module contexts, within the prescribed
60-second limit (40.7 s and 1.4 s respectively), with no reported errors or non-sorry warnings.

## Second reading by Q156

I reread the node, the Stacks lemma-finite statement and proof, and the complete Lean
signature after compilation. This is the dispatcher's single-worker self-check, not an
independent agent review; the brief forbids starting other agents and the maintainer's
independent review follows delivery. The field, both k-scheme structures, the commuting
k-morphism, target separatedness, source properness, the source dimension inequality,
the dimension-one restriction on components, two distinct image points, and finiteness
of f each occur exactly once as described above. The two occurrences of dimension use
the recorded `topologicalKrullDim`, including the subspace Z. The image condition is on
points of Y, not merely distinct source points or nonconstancy as a k-morphism. No mismatch
was found and no signature correction was made. The seven proof steps are preserved in
the docstring; all theorem proof content is postponed with `sorry`.
