## Worker report

The module `Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages` states
`AlgebraicGeometry.Etale.openImmersion_higherDirectImages_constructible_vanishing`.
It has one theorem with the whole proof `sorry`, no definitions and no auxiliary assertions.
The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`.
- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  `(N : ℕ) (hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))` uses the recorded
  convention: N is positive, kills Λ, and is invertible on Spec k, hence in k. No
  characteristic-zero, nonzero coefficient ring, prime-power or field-coefficient
  restriction is imposed.
- U and X are `Scheme.{u}` with `Over (Spec (.of k))` structures. For each, its structure
  morphism has `LocallyOfFiniteType` and `QuasiCompact`, exactly finite type.
- `(j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]` is the open immersion
  between these k-schemes. No separatedness or density hypothesis is imposed.
- F is `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, with
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. This is the recorded finite
  stratification with finite constant module values. Thus the word finite does not
  mean finitely many global sections, nor a uniform cardinal bound across all stalks.
- Throughout, R^q j_*F is written explicitly as
  `(DerivedCategory.homologyFunctor _ q).obj
  ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) j).obj
  ((DerivedCategory.singleFunctor _ 0).obj F))`.
  This uses the module direct image, with the same coefficients and category throughout.
  The unbounded total derived functor on F[0] computes the same higher direct images
  as its bounded-below version; it is also the exact expression used by the recorded
  finite-coefficient corollary. No second higher-direct-image definition is introduced.
- The first conjunct is `∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (R^q j_*F)`.
  The direct-image definition indexes cohomology by integers. Negative degrees are zero
  for a sheaf in degree zero, so including them does not strengthen the mathematical claim.
- The second is `∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (R^q j_*F)`: one bound works for
  the whole sheaf, not bounds varying with points or test objects.
- The third is `∀ q : ℤ, 0 < q → IsZero ((upperStar (ModuleCat Λ) j).obj (R^q j_*F))`.
  It asserts vanishing of the restriction as a module sheaf and does not assert
  vanishing of R^0 j_*F on U.

Recorded dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, imports the exact
  predicate `Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`. The theorem writes out its
  constructibility and upper-bound clauses, without asserting an additional lower bound.
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`,
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`, includes bounded constructible
  complexes and the other ambient vocabulary through public imports.
- `def-weil-pbc-scheme-conventions` is a convention node with no own declaration.
  `Scheme`, `Scheme.Over`, `Scheme.Hom.IsOver`, `LocallyOfFiniteType`, `QuasiCompact`
  and `IsOpenImmersion` are the standard Mathlib notions it specifies.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
  The recorded derived name has moved from the older record's module to
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; the server source
  was read with `scompile.py --source`. Its `rightDerivedLowerStar` is definitionally
  the generic `Functor.rightDerivedFunctor` applied to that same `lowerStar`.
  Importing this current public interface supplies the recorded construction.
- Proof-only imports retain the existing proof plan:
  `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
  (`isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`),
  `Sheaf.AlgebraicGeometry.OpenImmersionRestriction` (`openImmersion_restriction_leray`),
  and `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
  (`AlgebraicGeometry.etaleInverseImageModulesExact`). The cohomology-sheaf dependency
  is a Mathlib leaf, `DerivedCategory.homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, already imported publicly
  through the ambient derived categories. No import cycle was introduced.

Edge cases checked before writing: empty U and empty X are allowed; the identity open
immersion is allowed; zero F and the zero coefficient ring are allowed; N = 1 correctly
forces the zero coefficient ring. Characteristic zero and positive characteristic with
N invertible are both admitted. Positive-degree restriction vanishing excludes q = 0,
as required (for the identity, R^0 j_*F restricts to F). The conclusion asks no uniform
bound independent of F or X. Nonseparated finite-type schemes are allowed. The module
universe u+1 is the existing small-etale coefficient convention and allows all finite
rings and finite-stalk modules. Every universe and variable is explicitly bound.

Searches made:

- `msearch.py leansearch`: “higher direct images of constructible etale sheaves under
  an open immersion are constructible and vanish in high degrees”. The service returned
  Internal Server Error; this is recorded as unavailable, not evidence of absence.
- `msearch.py leanfinder`: “derived direct image open immersion finite constructible
  etale”. Eight results concerned constructible images of subsets and locally finite
  type/presentation of open immersions; no higher-direct-image finiteness statement.
- `msearch.py loogle`: `IsOpenImmersion, rightDerivedLowerStarPlus,
  isBoundedConstructible, DerivedCategory`. The service reported unknown identifier
  IsOpenImmersion, so this query supplies no absence evidence.
- A valid follow-up `msearch.py loogle` query, `"rightDerived"`, returned 12 generic
  right-derived-functor declarations (including `Functor.HasRightDerivedFunctor` and
  `Functor.totalRightDerived`), none giving this finiteness or restriction statement.
- `msearch.py grep`, scoped to Mathlib/AlgebraicGeometry:
  `open.*immersion|OpenImmersion|openImmersion|boundedConstructible|isBoundedConstructible`.
  Hits concerned scheme restrictions, opens and locally finite presentation, not this
  theorem. Local rg searches of the upstream and Sheaf trees for constructibility,
  boundedConstructible, open-immersion direct images, higher-image restriction and
  `thm-fin-open-immersion` found the two upstream results below and the recorded
  finite-coefficient corollary. The proposed new declaration name has no match in
  the upstream source, `dag/lean_names_upstream.json`, or `lean/Sheaf`.

Existing upstream candidates read in full:
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` contains
`boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion`
and `isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor`. The first uses
`Scheme.IsConstructibleSheaf` and `DerivedCategory.boundedConstructible`, whereas the
recorded dependency explicitly uses `Scheme.IsConstructibleEtaleModuleSheaf` and
`DerivedCategory.isBoundedConstructible`; their equivalence is a separate theorem,
not definitional. The second gives the restriction assertion alone with no finiteness
clause. Neither is the whole statement with the required recorded notions. The existing
finite-coefficient corollary gives bounded constructibility for arbitrary complexes but
has no restriction-vanishing clause. Hence no exact existing declaration is recorded.

The blueprint node and its unit source were read from the launcher's literature cache,
as the shared clone contains only the literature indices. The module docstring carries
all four expanded DAG proof steps. No new nodes, dependency modules, statement corrections,
or STATEMENT-DISPUTED flags are needed. The direct-image and inverse-image constructions
are reused, not copied.

Validation: the prescribed `scompile.py NV thm-fin-open-immersion` invocation compiled
both the sandbox probe and the module successfully, with no errors or warnings. The
module has no lines over 100 characters; the node's signature is extracted verbatim
from the theorem declaration. The required `deliver2.py --no-push` dry run is the final
worker check; the independent second reader supplies their own reading and delivery.

## Second reading by NV

I independently read the sandbox node and Lean module, the shared node and all its
statement-dependency records, the actual dependency declarations, and the blueprint
source at `sec-smooth-purity/sk-prop-sf-finiteness/thm-fin-open-immersion.md` in
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/`. I also read
that unit's `_section.md` and the source of `sbc-def-coefficient-conventions`.
The item itself has a blueprint source, not a Stacks theorem as its primary source.
For the proof's Stacks reference I read `sites-modules.tex`,
`lemma-flat-pullback-exact` (Tag 04JC), including its hypotheses and proof: inverse
image on abelian sheaves is exact, and module pullback is exact for a flat ringed
morphism. Here the constant coefficient comparison is an isomorphism, as specified
by the recorded module-exactness dependency; no flatness assumption on j is added.

The node's complete object/hypothesis/conclusion list, matched independently:

- Field k: `(k : Type u) [Field k]`. Verdict: exact, no algebraic/separable closure
  or characteristic assumption.
- Finite allowable coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`,
  `(N : ℕ)` and `hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`.
  I opened `SmoothBaseChangeCoefficients.lean`: the predicate is precisely
  `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(Spec (.of k), ⊤))`.
  Global sections of Spec k identify with k, so this is the source's positive
  annihilator invertible in k. The finite instance repeats a condition already
  supplied by hΛ; it adds no restriction. Verdict: exact coefficient convention.
- U and X finite-type k-schemes: `{U X : Scheme.{u}}` with both `Over` instances
  and, for each structure map, `LocallyOfFiniteType` and `QuasiCompact`.
  These are the standard Mathlib finite-type conditions (the scheme-conventions
  node introduces no competing definition). Verdict: exact; separatedness,
  reducedness, connectedness, affineness and density are not assumed.
- Open immersion j between these k-schemes: `(j : U ⟶ X)` with
  `[j.IsOver (Spec (.of k))] [IsOpenImmersion j]`. Verdict: exact morphism and
  compatibility with the two base structures.
- Finite constructible Λ-sheaf F on U_et:
  `F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
  I opened `BoundedConstructibleComplexes.lean` and its imported
  `IsConstructibleEtaleModuleSheaf.lean`: the latter requires a finite locally
  closed constructible stratification and etale-local constant finite module
  values on each stratum. This is precisely the recorded constructibility
  notion, with finiteness of local values, not finiteness of all sections.
  Verdict: same category and predicate as the node's dependencies.
- Higher direct image R^q j_*F: in all three clauses it is
  `(DerivedCategory.homologyFunctor _ q).obj
  ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) j).obj
  ((DerivedCategory.singleFunctor _ 0).obj F))`.
  I opened `UpperLowerStar/Defs.lean`: `lowerStar` is composition with the
  etale base-change functor, whose displayed objectwise formula is
  F(W ×_X U), and `upperStar` is its left adjoint.
  In `Derived/UpperLowerStarCoherence.lean`, `rightDerivedLowerStar` is
  `(lowerStar A j).rightDerivedFunctor`, and `rightDerivedLowerStarPlus` is
  the bounded-below version of the same functor. Thus the unbounded expression
  on F[0] is the same higher direct image through the existing plus-compatibility
  interface, and not derived abelian pushforward substituted for module pushforward.
  I also read the derived-category module and the Mathlib homology-functor
  interface. Verdict: correct cohomology sheaves of the canonical direct image.
- Every R^q j_*F constructible: the first conjunct quantifies `∀ q : ℤ` and
  applies `Scheme.IsConstructibleEtaleModuleSheaf` to that exact expression.
  The direct-image dependency itself defines R^q for integer q; negative degrees
  of the derived image of a degree-zero sheaf vanish. Verdict: all requested
  degrees, with no different notion of constructibility.
- Eventual vanishing: the second conjunct is `∃ b : ℤ, ∀ q : ℤ, b < q → IsZero`
  of the same higher direct image. Verdict: a single global bound for this F and
  j, in the correct quantifier order; neither a pointwise bound nor a numerical
  bound independent of the data is asserted.
- Positive-degree restriction vanishing: the third conjunct is
  `∀ q : ℤ, 0 < q → IsZero ((upperStar (ModuleCat.{u + 1} Λ) j).obj ...)`.
  Verdict: restriction to U in the same module category, exactly for q > 0.
  In particular the statement does not kill the degree-zero restriction F.

Proof dependencies were read as well. The recorded finite-coefficient corollary
in `OpenDirectImageFiniteCoefficients.lean` uses this same coefficient predicate,
module derived pushforward and `DerivedCategory.isBoundedConstructible`; it applies
in degree zero. `OpenImmersionRestriction.lean` supplies the underived abelian
counit as its first conjunct. `EtaleInverseImageModulesExact.lean` gives the
constant-ring comparison, exact module inverse image and compatibility of its
adjunction with the abelian adjunction. `DerivedCategory.homologyFunctor` is the
recorded Mathlib cohomology functor. The statement docstring reproduces all four
DAG proof steps: degree-zero finiteness, injective representative, degreewise
module counit, and exactness commuting with kernels/images/quotients. No proof
step or required proof import is missing.

Edge cases: empty U and empty X, the identity immersion, and zero F are allowed;
there are no Nonempty hypotheses. An empty finite stratification is permitted
for the empty scheme. No index-set assumption is introduced. N = 0 is excluded
exactly by the source's positivity convention. N = 1 allows precisely the zero
coefficient ring, and no Nontrivial hypothesis rules it out. In characteristic p,
the invertible annihilator is prime to p; characteristic zero is also covered.
The restriction assertion excludes q = 0, and its integer quantifier covers every
positive degree. Schemes and their field have arbitrary universe u; module values
and coefficients use the established u+1 small-etale convention. Finite rings and
finite module stalks admit this size convention; there is no independent smaller
test universe or extra equality of object/morphism universes. Every variable and
universe in the displayed signature is bound explicitly.

Independent H4 searches (with wording different from the worker's):

- LeanFinder via msearch: `etale sheaf open embedding derived pushforward cohomology
  finite constructible support complement`. Eight hits concerned topological
  open-embedding sheaf conditions, scheme module restriction, etale loci and
  constructible-image/topological facts. None states these three assertions.
- Loogle via msearch: `"homology", "IsZero"`. Twelve hits concerned short-complex
  homology, single-complex vanishing and generic derived-category degree bounds;
  none is the open-immersion finiteness/restriction theorem.
- LeanSearch via msearch: `cohomology sheaves of derived pushforward along open
  embeddings with finite torsion coefficients are constructible`. The service
  returned Internal Server Error; unavailable, not evidence of absence.
- Mathlib grep via msearch, scoped to AlgebraicGeometry:
  `higherDirectImage.*[Oo]pen|[Oo]pen.*higherDirectImage|constructible.*[Pp]ushforward`:
  no hits. Local rg searches in the Mathlib AlgebraicGeometry, upstream
  WeilConjectures and shared lean/Sheaf trees also inspected higher-direct-image
  terminology and located the candidates below. Exact name and blueprint-id
  searches found no existing shared theorem for this item.

I opened the two relevant upstream declarations in full in
`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`:
`boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion`
uses `Scheme.IsConstructibleSheaf` and `DerivedCategory.boundedConstructible`,
not the DAG's finite-stratification predicate, and states only bounded
constructibility. `isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor`
states restriction vanishing alone (even for q ≠ 0). Neither is the whole
statement in the required dependency notions. The existing
`OpenDirectImageFiniteCoefficients` theorem has no restriction clause.
`Paper/RestrictionDirectImage.lean` instead concerns a pro-etale restriction
under a FIN bound and is a different statement. Thus the new item module is
appropriate; no duplicate definition, replacement dependency or new node is needed.

Mismatches found: none. Changes: appended this independent second-reading record;
the Lean module and node were left as written. There is no statement_change, new
definition node or dependency module to audit under H12/H13. The theorem has only
`by sorry`; no definition has postponed data and nothing is proved. Source/blueprint
docstrings, namespace, imports and 100-character line widths meet the conventions.
The node's lean.statement was checked programmatically to equal the complete
signature verbatim, from `theorem` to immediately before `:= by`.

Second-reader validation: `scompile.py NV thm-fin-open-immersion
lean/Sheaf/AlgebraicGeometry/OpenImmersionHigherDirectImages.lean` succeeded:
the sandbox probe compiled in 34.4 seconds and the delivered module in 16.1 seconds,
with no errors or warnings. No direct compiler or global build was run.
