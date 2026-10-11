## Worker report

The module introduces `AlgebraicGeometry.MeromorphicSheaf` and states
`meromorphicSheaf_generic_product`. It imports Mathlib's `IsLocallyNoetherian`,
`genericPoints`, and the project's `Scheme.Modules.IsInvertible`. The generic-point
hypothesis is rendered by `η ∈ genericPoints X.carrier`; the stalk clause is rendered
using `TopCat.Presheaf.stalk` through `M.presheaf.stalk η`. The invertible-module
binder is `(L : X.Modules) [L.IsInvertible]`.

The meromorphic-sheaf notion is absent from Mathlib and the source Lean, so a new
definition node was added. Searches used grep for `meromorphic` and `nonZeroDivisor`
in Mathlib and `WeilConjectures`; no matching sheaf declaration was found.

## New nodes

`def-sc-meromorphic-sheaf` records the source notion from Stacks Tag 0EMH and
supplies the module declaration used by the item.

## Earlier second reading (a previous round; superseded)

The item imports the new meromorphic-sheaf declaration and renders its binders and generic-point stalk equality as recorded.

## Second reading by M1

I independently opened the base node, its sandbox copy, both original modules, every
statement dependency record and the declaration source of each dependency with a Lean
record. The original delivery was not the node's statement. The base node itself is
correct; no statement correction is needed. The original Worker report and New nodes
paragraph above describe the superseded draft, not the final delivery.

Source reading: the repository has no local divisors.tex. I fetched the Stacks source
into this item's scratchpad/divisors.tex and read lines 6035 onward (0EMF) and 6315
onward (0EMH), together with the surrounding definitions of regular denominators and
meromorphic modules. I also opened the Stacks tag pages. Tag 0EMH assumes exactly a
locally Noetherian scheme with no embedded points; there is no base field, separatedness,
quasi-compactness, reducedness or characteristic hypothesis. The node is the sectionwise
product assertion specialized to an invertible module, with its canonical stalk and action
identifications. It does not request the source's additional quasi-coherence or rational
function conclusions.

Object, hypothesis and conclusion checklist (all verdicts refer to the repaired module):

- Scheme X: `{X : Scheme.{u}}`, matching def-pc-scheme. Pass.
- Locally Noetherian: `[IsLocallyNoetherian X]`, the recorded Mathlib class in
  Mathlib.AlgebraicGeometry.Noetherian. Read its affine-open formulation; it imposes
  precisely local Noetherianity, not global Noetherianity. Pass.
- No embedded points: `h_no_embedded` applies only to points whose maximal ideal is
  the annihilator of an element, expressed literally by `∃ a, ∀ r,
  r ∈ IsLocalRing.maximalIdeal ... ↔ r * a = 0`. Its conclusion is membership in
  `genericPoints X`. This matches the associated-point definition written in
  lem-sc-ass-weakass-locally-noetherian, without the stronger assertion that every
  point is generic. No private associated-point predicate was introduced. Pass.
- X^0 and its components: `genericPoints X` is Mathlib's set
  `{x | closure {x} ∈ irreducibleComponents X}` (Sober.lean:277).
  `IsGenericPoint` is closure equality (Sober.lean:39). These are exactly the
  notions of def-sc-generic-point and def-weil-irreducible-components. Pass.
- Invertible L: `(L : X.Modules) [L.IsInvertible]`, using the recorded
  Scheme.Modules.IsInvertible from WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  whose signature asks for local structure-sheaf trivializations. Pass.
- K_X: `K := meromorphicModule X (unit X)`. I read the entire landed
  Sheaf.AlgebraicGeometry.MeromorphicModule, including meromorphicDenominators,
  meromorphicPresheaf, meromorphicFraction and toMeromorphicModule. It sheafifies
  the module localizations at the sections whose germs are non-zero-divisors, as
  in Tags 01X2 and 01X4. `unit X` is the existing structure-sheaf module, not
  the meromorphic sheaf. Pass.
- K_X(L): `KL := meromorphicModule X L`. The same dependency's
  `meromorphicModule_tensor_iso` identifies this with `K ⊗ L` for invertible L.
  This is the existing notion recorded by def-sc-meromorphic-module, now added
  to the item's stmt_deps. No replacement tensor or localization definition. Pass.
- Stalks: `K.presheaf.stalk η.val`, `KL.presheaf.stalk η.val`,
  `X.presheaf.stalk η.val`, and `L.presheaf.stalk η.val` use the Mathlib stalks
  named by def-weil-pbc-module-stalk. The existential families `eK` and `eL`
  are additive equivalences in the required directions for every generic η.
  The first two conjuncts normalize them on the canonical localization maps
  of ordinary sections; they cannot be arbitrary identifications. Every ordinary
  stalk element is a germ, so this normalization fixes the inverse of the
  canonical stalk map. Pass.
- Every open U and both section bijections: the next two conjuncts assert
  Function.Bijective for the actual germ maps followed by eK/eL. Their target
  functions range over `{x : X // x ∈ genericPoints X ∧ x ∈ U}` and land in
  O_{X,x} and L_x respectively. Thus these are the full dependent products,
  not finite products, selected sections, or merely abstract equicardinality. Pass.
- Restriction compatibility: the fifth conjunct quantifies over every inclusion
  `i : V ⟶ U` and every generic η in V, and equates the identified germ of
  the restricted section with the identified original germ for both K and KL.
  This is precisely coordinate deletion in the products. Pass.
- Meromorphic scalar action and `(ft)_η = f_η t_η`: `mul U` acts on K(U) and
  KL(U), not just O_X(U) and L(U). The local fraction conjunct requires
  `(a/b)(m/c) = (a • m)/(b*c)` via the existing meromorphicFraction maps.
  The next conjunct requires these operations to commute with all restrictions.
  Fractions locally represent every section of the sheafifications, so these
  two clauses characterize the canonical meromorphic multiplication uniquely;
  they do not introduce an unrelated action via an arbitrary bijection. The
  final conjunct asserts its germ formula for every U, η, s and t. The scalar
  multiplication on L's stalk is Mathlib's existing PresheafOfModules instance,
  exposed by inferInstanceAs after unfolding L.presheaf; it is not assumed as
  an additional hypothesis. Pass.

Edge cases: the empty scheme and empty open are included (no Nonempty binder).
The generic-point index is an unrestricted subtype, and an empty product is the
unique empty function. Nilpotent generic local rings are included: no IsReduced,
IsDomain or Field instance occurs. There is no bound on the number of components,
no restriction on characteristic, and no n parameter. The sole universe u is
explicit throughout; invertible modules are locally rank one over O_X and their
stalks and sections have the existing universe of X.Modules. No variables or
universes remain implicit. A zero sheaf can be invertible on the empty scheme and
is covered. On a nonempty scheme an invertible sheaf is locally O_X, so the zero
module case is correctly excluded by invertibility itself, not an added binder.

Independent searches (2026-10-11):

- LeanSearch via msearch.py: "meromorphic sections generic points locally
  Noetherian scheme without embedded points". The service returned Internal
  Server Error; recorded as unavailable, not as a no-match result.
- LeanFinder via msearch.py: "sheaf of total quotient rings is product of
  generic point stalks". Eight candidates, including totalQuotientPresheaf,
  localizationToStalk_mk', stalkIso and germToFunctionField. I inspected the
  relevant candidates: the total quotient declaration is an unsheafified
  presheaf, while function-field declarations assume irreducibility and do
  not give this general product theorem.
- Loogle via msearch.py: "TopCat.Presheaf.totalQuotientPresheaf". It returned
  totalQuotientPresheaf, toTotalQuotientPresheaf and the Mono instance. None
  states the generic-point product theorem or replaces meromorphicModule.
- Grep via msearch.py: "totalQuotientPresheaf|meromorphicModule|meromorphicSheaf_generic_product"
  found only the Mathlib presheaf declarations. Independently rg on the
  project's lean/Sheaf and source WeilConjectures found the landed
  meromorphicModule and its tensor identification, and no generic-product
  statement. rg on dag/nodes found def-sc-meromorphic-module already carries
  exactly the missing notion. Name search on dag/lean_names_upstream.json,
  Mathlib and WeilConjectures found no collision with the final theorem name.

Mismatches and repairs:

1. H4/H12: the new def-sc-meromorphic-sheaf duplicates the already landed
   def-sc-meromorphic-module. Removed its sandbox node and module; replaced
   the item's added dependency by def-sc-meromorphic-module. There are no new
   definition nodes or dependency modules in the final delivery.
2. H3/H5: the old MeromorphicSheaf was defined as unit X, hence was O_X,
   not its localization sheaf. Removed it and used the real existing definition.
3. H3: the old h_no_embedded said every point is generic. Replaced it by
   the exact associated-point implication above.
4. H3: the sole old conclusion was reflexive equality of K's stalk with
   itself. Replaced it by both canonical stalk identifications and both
   sectionwise germ bijections for every open.
5. H3: the old theorem omitted restrictions and the module action entirely.
   Added both compatibility clauses and characterized multiplication by its
   fraction formula, so the final action equation has the node's meaning.
6. H8/H9: added the project header, module source docstring, full three-step
   node proof in the theorem docstring, explicit universe, and 100-column
   formatting. The only proof is the named theorem's `sorry`.
7. Compilation exposed the stalk-action instance through L.val.presheaf rather
   than the wrapped L.presheaf. An explicit letI uses the existing instance
   with Ab.{u}; a noncomputable section permits its colimit-based construction.
   This adds no hypothesis and no new definition.

The node's mathematical statement is unchanged, and its lean.statement is copied
verbatim from the final theorem signature. All original statement dependencies
are retained. The final delivery contains only the item's module, node and report.
