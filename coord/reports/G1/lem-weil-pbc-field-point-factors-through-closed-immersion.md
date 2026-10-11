## Worker report

The module `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion` states the
field-valued point factorization lemma. It uses Mathlib's `Scheme`, `Spec`, and
`IsClosedImmersion` declarations. The binders `{X Z : Scheme.{u}}`, `(i : Z ⟶ X)`, and
`[IsClosedImmersion i]` render a closed immersion of schemes. The binders
`{K : Type u} [Field K]` render a field, and `s : Spec (CommRingCat.of K) ⟶ X` is the
field-valued point. The point `z : Z` and hypothesis
`h : s.base (default : Spec (CommRingCat.of K)) = i.base z` render that the unique
point of `Spec K` maps to `i(z)`. The conclusion is `∃! s'`, with conjunction clauses
`s' ≫ i = s` (factorization) and
`s'.base (default : Spec (CommRingCat.of K)) = z` (the lifted point is `z`).

The statement dependency declarations are Mathlib leaves: `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.IsClosedImmersion`, and `AlgebraicGeometry.Spec`/`Spec.map`.
No project dependency module is required. The field edge case is covered by Mathlib's
`Unique (Spec (CommRingCat.of K))` instance; the arbitrary universe is represented by a
single explicit universe `u` shared by the scheme and field types. The empty scheme and
zero-ring cases are excluded exactly as in the node because a field is nontrivial.

Searches for an existing declaration: `msearch.py leanfinder` for field-valued points
factoring through closed immersions found only `IsClosedImmersion.lift` (which requires
a kernel inclusion); `msearch.py loogle` for `AlgebraicGeometry.IsClosedImmersion.lift` found four
kernel-condition lift results, with no direct theorem; grep of Mathlib's
`AlgebraicGeometry` morphism files found no set-theoretic field-point factorization; rg
of `WeilConjectures/` and `lean/Sheaf` found no declaration matching this lemma.
The module compiles cleanly with the expected `sorry` proof.

The source checkout also has
`AlgebraicGeometry.IsClosedImmersion.existsUnique_fac_of_field` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
It gives unique factorization from range membership, but does not state the specified-point
clause for `z`. The present statement includes that clause explicitly; it introduces no
new definition. The source module and complete signatures were inspected.
LeanSearch returned Internal Server Error (unavailable). LeanFinder returned eight hits
including `IsClosedImmersion.lift`; Loogle for that name returned four kernel-condition
lift lemmas. The grep query `existsUnique_fac_of_range|lift_of_range|le_ker_iff_range_subset`
in Mathlib/AlgebraicGeometry returned zero hits. Source and project rg searches were also
performed. Stacks Tag 0356 and Tag 01J9 were read online because the local Stacks source
is absent: https://stacks.math.columbia.edu/tag/0356 and
https://stacks.math.columbia.edu/tag/01J9.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader designated by the dispatcher. The worker has not
claimed an independent review.


## Second reading by G1

Independent second reader, 2026-10-11. I opened the item node and module, all three
statement dependency nodes and their Mathlib declarations, and the upstream candidate.
Verdict: the Lean says exactly what the node says. No statement or code repair is needed.

Objects, hypotheses and conclusion, matched individually:

- Arbitrary schemes X and Z: `{X Z : Scheme.{u}}`. PASS. `def-pc-scheme` is the
  Mathlib leaf `AlgebraicGeometry.Scheme` / `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`: the locally affine locally ringed space and
  its locally ringed-space morphisms, not a scheme over an unstated base.
- The morphism i from Z to X: `(i : Z ⟶ X)`. PASS, with the correct direction.
- Closed immersion: `[IsClosedImmersion i]`. PASS. I read
  `def-weil-closed-immersion` and `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion` means a closed embedding and surjective stalk maps.
  `isClosedImmersion_iff_isAffineHom` gives the dependency node's equivalent
  affine description by surjective section maps. No extra affineness is assumed.
- An arbitrary field K: `{K : Type u} [Field K]`. PASS. Nontriviality belongs to
  the field definition; no algebraic closure, characteristic or extension is assumed.
- Its spectrum and field-valued point: `(s : Spec (CommRingCat.of K) ⟶ X)`.
  PASS. I read `def-weil-affine-spectrum`, Mathlib's `Spec`, `Spec.map`, and
  `Spec.homEquiv`: the actual affine scheme of prime ideals, contravariant in
  rings. `Scheme.lean:627` supplies `Unique (Spec (.of K))`.
- A specified point of Z: `(z : Z)`. PASS: Scheme's coercion is its underlying
  topological space, not a rational point or a closed-point predicate.
- The image-point hypothesis: `(h : s.base (default : Spec (CommRingCat.of K))
  = i.base z)`. PASS. `default` denotes the unique prime-spectrum point, so
  this is precisely s(xi) = i(z); it is not a scheme-theoretic containment hypothesis.
- Existence of a lift with the same field: `∃! s' : Spec (CommRingCat.of K) ⟶ Z`.
  PASS: the field is fixed before the existential, with no field extension.
- Factorization: `s' ≫ i = s`. PASS: CategoryTheory composition is i after s'.
- Specified-point clause: `s'.base (default : Spec (CommRingCat.of K)) = z`.
  PASS. This is explicitly present and refers to the same z as the hypothesis.
- Exactly one morphism factoring through i: `∃!` on the conjunction above.
  PASS. Every factorization automatically satisfies the point clause, since
  i is injective on points and i(s'(xi)) = s(xi) = i(z). Thus uniqueness for
  the conjunction is equivalent to uniqueness among all factorizations, as
  the node requires; it does not silently weaken that uniqueness.

Source check: the local repository has no Stacks checkout. I fetched the actual
`schemes.tex` into sandbox `scratchpad/schemes.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex and
read the surrounding sections, not only the tag statements. The label
`lemma-map-into-reduction` (Tag 0356) assumes an arbitrary scheme X, a closed
subscheme Z and a reduced source Y; Spec K is reduced. There is no standing
Noetherian, separatedness, finiteness or base-field hypothesis. The discussion
before `lemma-characterize-points` (01J9) gives the point/residue-field-map
correspondence used in the node proof. `definition-closed-immersion-locally-ringed-spaces`
(01HK) gives injectivity, and `lemma-immersions-monomorphisms` (01L7) gives
uniqueness. I also verified the published tag pages:
https://stacks.math.columbia.edu/tag/0356,
https://stacks.math.columbia.edu/tag/01J9,
https://stacks.math.columbia.edu/tag/01HK,
https://stacks.math.columbia.edu/tag/01L7.

Edge cases: empty X and empty Z are permitted by the scheme binders, with no
`Nonempty` assumption. For empty Z there is no input z; for empty X there is no
morphism from the nonempty Spec K. These cases are vacuous, not excluded by an
extra hypothesis. This corrects the worker report's claim that empty schemes
are excluded because fields are nontrivial. Zero rings are not fields, as in
both the node and source specialization. Z need not be reduced, and X may have
nilpotents. All characteristics and the identity closed immersion are covered.
There is no index set or n in this statement. The explicit arbitrary universe u
is the universe of Mathlib's category of schemes and commutative rings; it is
not fixed to Type 0 or restricted by finiteness. All objects of a morphism are
in that common category, and no variable or universe is unbound.

Independent H4 searches (different queries from the first worker):

- LeanFinder: `Spec of field lift into closed subscheme with prescribed image point`.
  Eight hits, including `SpecToEquivOfLocalRing_apply_fst`,
  `IsClosedImmersion.Spec_iff`, affine image factorization, and `liftQuotient`;
  no exact statement with the specified-point clause.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, ∃! _, _`: zero hits.
- LeanSearch: `A field valued point of a closed subscheme has a unique lift with
  the prescribed image point`: service unavailable (Internal Server Error),
  recorded by msearch as unavailable, not as an absence verdict.
- rg over Mathlib/AlgebraicGeometry, WeilConjectures/, the project's lean/Sheaf,
  and dag/lean_names_upstream.json for `field_point_factors`,
  `existsUnique_fac_of_field`, `existsUnique_fac_of_range`, and conceptual
  closed-point/factor/immersion combinations. The upstream theorem
  `AlgebraicGeometry.IsClosedImmersion.existsUnique_fac_of_field` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:204`
  assumes range membership at `IsLocalRing.closedPoint K` and concludes
  `∃! t, t ≫ i = s`. I opened its full signature and surrounding declarations.
  It has neither an introduced z nor the explicit clause t(xi) = z. It is a
  useful proof dependency, but does not have exactly this node's full statement;
  retain the present statement module rather than recording that partial match
  as an existing exact declaration. There are no new notions or private copies.

H5-H9: one named theorem with `sorry`, no definitions or hidden data, and nothing
proved. Its declaration and module docstrings cite the source and blueprint id.
The proof docstring follows all four node steps: point/field-map setup and the
residue isomorphism, construction via naturality and contravariant Spec,
injectivity for the point of any lift, and uniqueness from the field-map
correspondence. The import is used, namespace is AlgebraicGeometry without a
Sheaf prefix, and every line is at most 100 characters. No new definition nodes,
dependency modules or statement corrections occur in this delivery.

Changes: appended this independent review and corrected the worker report's
empty-scheme explanation here; preserved the correct Lean and node record.
Verified programmatically that `lean.statement` is verbatim the file signature.
Server scompile passed cleanly in 1.6 seconds with no errors or warnings.
