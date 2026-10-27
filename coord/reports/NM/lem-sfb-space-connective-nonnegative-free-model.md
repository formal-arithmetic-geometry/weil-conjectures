## Worker report

Item: lem-sfb-space-connective-nonnegative-free-model. Group NM, stage 2,
2026-10-24. The delivery states
`AlgebraicGeometry.AlgebraicSpace.exists_etale_nonnegative_finiteFree_model` in
`Sheaf.AlgebraicGeometry.SpaceConnectiveNonnegativeFreeModel`. Its only proof is
`sorry`. There are no new definitions, auxiliary theorems, or dependency repairs.

Source read: Stacks `literature/stacks-project/quot.tex`,
`lemma-cohomology-perfect-complex` (08JX), including the final cokernel argument,
the finite locally free trivialization, and the matrix formula. The DAG lemma
starts with perfectness already established and extracts the local-model step.
The module docstring records all seven steps of its accepted DAG proof, including
the square-zero-algebra test which converts scheme-test vanishing into the module
flat-opcycles criterion. No statement correction or disputed clause is needed.

Clause-by-clause rendering:

- The size convention is `universe u w`. Schemes, rings, and module sections use
  `u`, while derived localizations have arbitrary morphism universe `w`.
  `[HasDerivedCategory.{w} B.SmallModules]` and the corresponding family for
  represented schemes choose the localizations required to state all the tests.
  These are size/choice data, not finiteness or geometric restrictions. The family
  index `I : Type u` is small in the prescribed small-site universe.
- The base scheme is `{S : Scheme.{u}}`; the space is `(B : AlgebraicSpace S)`.
  The site's structure modules are the existing `B.SmallModules`. This is exactly
  the recorded equivalent small affine ringed model of `B.Modules`; its structure
  ring sheaf is `B.smallStructureRings`, obtained from the actual regular functions.
- `(K : B.DerivedModules)` is the object of the unbounded module derived category.
  `hperfect` is precisely the recorded
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  B.smallStructureSheaf K`, using bounded local finite-free retracts, not global
  boundedness or globally free terms.
- `hconnective` quantifies over every `T : Over S`, every
  `g : schemeSpace T ⟶ B`, and every `i : ℤ` with `i < 0`.
  It says `IsZero` of the `DerivedCategory.homologyFunctor` of the canonical
  `(spaceDerivedPullback g).obj K`. No flatness or etaleness is assumed of `g`.
  Every scheme test into B has its induced structure map into S, so `Over S`
  loses no test. `spaceDerivedPullback` is the existing total left derived
  tensor pullback; its K-flat computation is part of the chart-calculus input.
- The conclusion chooses `I`, commutative coordinate rings `A : I → CommRingCat`,
  maps `s a : Spec (A a) ⟶ S`, and `v a : schemeSpace (Over.mk (s a)) ⟶ B`.
  Thus every member is literally an affine spectrum, including the zero ring.
  `∀ a, IsEtale (v a).hom.hom` is representable etaleness on scheme base changes.
  `IsJointlySurjective (fun a ↦ (v a).hom.hom)` is the already recorded union of
  point images criterion, expressed by field-extension lifts.
- Inside `∀ a`, the existential integer `b` and `0 ≤ b` give the individual bound.
  `P` is a genuine cochain complex on the small etale ringed model of that affine
  scheme. `∀ n, n < 0 ∨ b < n → IsZero (P.X n)` gives exactly its support interval.
- `Nonempty ((spaceDerivedPullback (v a)).obj K ≅ DerivedCategory.Q.obj P)` gives
  an isomorphism of the actual derived objects. It is not a list of cohomology
  isomorphisms. `DerivedCategory.Q` is localization at quasi-isomorphisms.
- `r : ℤ → ℕ` gives the finite ranks. `e n` identifies `P.X n` with the finite
  product of `Fin (r n)` copies of `SheafOfModules.unit`. Finite products here are
  finite free structure modules; evaluation preserves these products, so their
  sections are finite tuples of structure-ring sections. Isomorphism is the
  invariant meaning of the informal identification with a free structure module.
- `m n : Matrix (Fin (r (n+1))) (Fin (r n)) (A a)` specifies every differential
  matrix with rows indexed by the next degree and columns by the present degree.
  The last equality is imposed for every n, chart W, section x, and row j.
  Its left side is the j-th coordinate of `P.d n (n+1)` in basis `e (n+1)`;
  its right side sums matrix coefficients times the k-th coordinate in `e n`.
  Coefficients are pulled from A to the actual chart's regular functions by
  `(Scheme.ΓSpecIso (A a)).inv` and `Scheme.Γ.map` of `chartToScheme` for the
  identity of the represented affine scheme. Thus the coefficients really lie in
  A and act by its canonical scalar map; no arbitrary scalar action is supplied.
  The product projection maps `Pi.π` make the equality independent of any
  implementation of tuples. The cochain-complex type enforces d composed with d=0.
- `b`, `P`, `r`, `e`, and `m` are all selected after the member `a`. There is no
  common bound, common rank, Noetherian condition, separation, or compactness input.

Dependency declarations used (the modules are public imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, the small
  etale regular-functions construction and module category.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently the
  Mathlib `SheafOfModules` carrier used by the small model.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, reused by the canonical derived pullback.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`; its definition uses the
  recorded `StrictPerfectCoefficientPackageOnSite` and localized bounded models.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its representative interpretation.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the existing
  actual representable sheaf of a scheme, owned by def-trf-scheme-algebraic-space.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallEtaleModel`,
  `smallEtaleInclusion`, `smallStructureSheaf`, `smallStructureRings`,
  `SmallModules`, and the fixed `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules` and
  `chartToScheme`, whose definition is the Yoneda preimage of the chart arrow.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.

The last five definition owners are already landed nodes added to stmt_deps as
per the standing rule allowing landed notions to be cited. No node was created,
no existing declaration was copied, and no dependency record was changed.
Proof dependencies with recorded modules are imported plainly; the Mathlib leaf
for the affine basis is `Mathlib.AlgebraicGeometry.AffineScheme`, and the finite
presentation/flatness leaf is `Mathlib.RingTheory.Flat.EquationalCriterion`.

Edge cases checked before drafting and on rereading:

- Empty B admits an empty index I; the family type has no Nonempty requirement.
- For the zero complex choose rank zero everywhere and b=0; empty sums and empty
  products give the expected zero differential and zero structure module.
- A complex in degree zero permits b=0; positive upper support is not required.
- Both zero source rank and zero target rank of a matrix are permitted by Fin 0.
- The zero ring and empty affine scheme are allowed by CommRingCat, with no
  Nontrivial assumption. Finite-rank identifications still have their usual meaning.
- A bounded complex `[A --a--> A]` in degrees -1,0 over a nonzero ring with a=0
  fails the universal hypothesis already on the identity test, so negative-degree
  terms cannot enter vacuously. A degree-zero quotient with nonzero Tor is also
  excluded by nonflat scheme tests (equivalently the square-zero-algebra argument).
- Infinitely many components with unbounded ranks or upper bounds are allowed:
  all such choices occur inside the chart quantifier.
- All test schemes and rings use the same universe as B's big site, avoiding a
  vacuous hypothesis caused by smaller independent test universes. w remains free.

Searches actually run:

1. msearch.py leanfinder: `universally connective perfect complex has etale locally
   bounded finite free model in nonnegative degrees`. Eight hits about etale ring
   maps/loci; no result about connective perfect complexes or these local models.
2. msearch.py loogle: `"CochainComplex", "Projective"`. Twelve hits, including
   `CochainComplex.isKProjective_of_projective` and K-projective stability. These
   do not give etale local finite free models in nonnegative degrees.
3. msearch.py grep: `nonnegative.*[Ff]ree|[Ff]ree.*nonnegative|connective.*[Pp]erfect`.
   Zero Mathlib hits.
4. rg of lean/WeilConjectures and lean/Sheaf for connective/perfect and
   nonnegative/free, plus the node id. Found the Zariski pointwise
   `FlatModelFiniteFreeShortening`, residue criteria, and Picard model lemmas.
   Read the shortening theorem: it assumes an already nonnegative flat complex
   and a free resolution on a Zariski open and compares pullback homology. It is
   not this algebraic-space universal-test theorem with a derived isomorphism.
5. grep -rn of the exact node id under lean/WeilConjectures: no match.
   rg of the intended full theorem name and connective/perfect patterns under
   dag/lean_names_upstream.json and both Lean roots: no duplicate theorem name.

Validation: scompile.py compiled the module in both sandbox and its intended
library name cleanly. The first draft's matrix formula used multiplication on a
module-valued coordinate; it was corrected to the canonical scalar action `•`.
All variables/universes are explicit (`set_option autoImplicit false`), every
line is at most 100 characters, and the single postponed proof is the item's
named theorem. Final delivery validation is recorded below.

## Second reading by NM

A sequential second reading was performed by this dispatcher worker; the prompt
forbids starting another agent. Independent mathematical review remains with the
maintainer, as the brief specifies. This paragraph does not claim a second agent.

Reread the node's complete statement and seven proof steps alongside the final
Lean signature. The hypothesis is perfectness on the ringed site, not an affine
perfectness assumption; universal connectivity includes all scheme tests. Every
cover member is Spec A, etaleness and joint surjectivity are both present, the
bound is an integer with 0≤b, the full complex is zero outside [0,b], and the
isomorphism is in D(O). Finite-free bases and matrices are given in every degree,
with the correct next-degree row/present-degree column orientation. In particular
the coefficient map is the canonical map from A to chart functions. Using `•`
fixes the type mismatch without altering that formula. Finite products express
finite free modules under the small-model equivalence; no extra local freeness
or projectivity hypothesis is substituted. The only metadata additions are five
already landed definition dependencies. No mathematical mismatch, missing clause,
statement correction, new definition node, or dependency-module repair was found.

Final dry run: `deliver2.py NM lem-sfb-space-connective-nonnegative-free-model
--no-push` printed `OK (dry run)` at commit 2a96663e00e: preflight passed and the
module compiled cleanly under its sandbox and library names. The packet contains
exactly this report, the item's node record, and its one Lean module.
