## Worker report

The module `Sheaf.Paper.FiniteFieldStratifiedPerfectModels` states
`AlgebraicGeometry.ProEtale.finite_field_stratified_perfect_models`, with proof `sorry`.
It introduces no definitions. The mathematical statement and proof of the node are unchanged.
The one added statement dependency is the already landed
`def-weil-pbc-proetale-operations`, to name ordinary restriction of the compared object
in the continuous-function coefficient-ring presentation. No new nodes or dependency repairs.

Hypotheses and clauses, matched against the complete node:

| Node text | Lean rendering |
| --- | --- |
| X is a scheme | `(X : Scheme.{u})` |
| X is Noetherian | `[IsLocallyNoetherian X] [CompactSpace X]`; exactly the two components of Mathlib `IsNoetherian X` |
| k is a finite field | `(k : Type (u + 1)) [Field k] [Finite k]` |
| Finite coefficients have the discrete topology for the pro-etale convention | `[TopologicalSpace k] [DiscreteTopology k]`; the discrete topology is unique and available for every finite field, and adds no field restriction |
| L belongs to D(X_et,k), modules over the constant ring sheaf | `L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k))`; this is the recorded fixed-ring module-sheaf encoding, identified with ringed modules by `finiteCoefficientEtaleRealization` |
| L is bounded | `hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor ... q).obj L)` |
| Every cohomology sheaf is constructible | `hconstructible : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf ((DerivedCategory.homologyFunctor ... q).obj L)` |
| A finite stratification by locally closed subschemes | `∃ S : Scheme.FiniteLocallyClosedStratification X`; this records the finite partition, disjointness, local closedness, cover, stratum schemes, immersions and their exact images |
| The strata are constructible | `(∀ i : Fin S.n, Topology.IsConstructible (S.stratum i))` |
| An etale covering on each stratum | `∀ i : Fin S.n, ∃ 𝒰 : Cover.{u} etalePrecoverage (S.domain i)`; a Cover is jointly surjective and all its structure morphisms are etale |
| On each member, a genuine complex of k-vector spaces | `∀ j : 𝒰.I₀, ∃ (P : CochainComplex (ModuleCat.{u + 1} k) ℤ) (a b : ℤ), ...`; the complex contains its differentials and square-zero identities |
| That complex is bounded | `P.IsStrictlyGE a ∧ P.IsStrictlyLE b`; these say terms outside the interval are zero, not just their cohomology |
| Its terms are finite-dimensional | `∀ q : ℤ, Module.Finite k (P.X q)`; over a field finite generation is precisely finite dimension |
| L restricted to the cover member is the constant complex | The first `Nonempty (... ≅ ...)`, with `(Etale.upperStar (ModuleCat k) (𝒰.f j ≫ S.immersion i)).mapDerivedCategory.obj L` and `DerivedCategory.Q.obj (((constantSheaf ... (ModuleCat k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)` |
| The model is perfect over k | `@DerivedCategory.IsPerfectRingComplex k _ (HasDerivedCategory.standard _) ((@DerivedCategory.Q ... (HasDerivedCategory.standard _)).obj P)`; this is the dependency's actual bounded finite-projective predicate, with explicit standard localization and no extra localization-existence hypothesis |
| The same models apply after nu_X^*, restricted to the same cover | The second `Nonempty (... ≅ ...)`: `(finiteCoefficientDerivedPullback X k (𝒰.f j ≫ S.immersion i)).obj ((finiteCoefficientDerivedComparison X k).obj L)` is isomorphic to the pro-etale constant complex for exactly the SAME P, followed by `(finiteCoefficientRealization (𝒰.X j) k).mapDerivedCategory` |
| No integral lifting or completeness hypothesis | There is no integral coefficient datum, ideal, lifting, completeness or adic assumption anywhere in the signature |

Restriction along the composite `𝒰.f j ≫ S.immersion i` is the canonical inverse image
of the restriction to the stratum, through the standard composition isomorphism.
The same bound variables need not be supplied by a consumer: the model is existentially
bounded as in the node. The two isomorphism clauses share P and its differentials, not
merely the list of cohomology objects. Pro-etale realization explicitly places the second
isomorphism in modules over `finiteCoefficientRingSheaf`, the sheafification of continuous
functions on connected components. It does not silently substitute a different coefficient
ring or an unspecified map.

Dependency interfaces read and used (including the source docstrings and definitions):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `AlgebraicGeometry.IsNoetherian` (the latter has exactly the two chosen hypotheses).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff condition).
- `Mathlib.Algebra.Field.Defs`: `Field` (the field node is a Mathlib leaf with no lean record).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, plus the homology functor.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`,
  `Scheme.etalePrecoverage`; covers use `CategoryTheory.Cover`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of Mathlib `SheafOfModules`; used through the finite-module APIs.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. Its actual definition uses
  `Scheme.Stratification`, which includes constructible strata; the global finite partition
  with finite module values is precisely the node's constructibility hypothesis.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`. Its lack of a constructibility
  field is why the conclusion supplies the separate constructibility conjunct.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`; this dependency is a
  Mathlib match, needing no lean record or repair.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, with arbitrary localization universe. Both it
  and its Q object use the same explicit `HasDerivedCategory.standard`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientDerivedComparison`. The latter is the exact termwise comparison followed
  by the canonical coefficient realization, as the node requests.
- Added landed node `def-weil-pbc-proetale-operations`, recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: its public closure includes
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`, whose
  `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedPullback` is the ordinary exact
  inverse image for precisely these finite continuous-function coefficients. It is
  `finiteCoefficientUnrealization ⋙ ProEtale.upperStar ⋙ finiteCoefficientRealization`
  descended termwise. These are existing canonical equivalences, not a newly chosen map.

All recorded proof-dependency modules are imported (proof-only imports are not public),
including the common-stratification refinement, etale inverse-image exactness, constant-module
naturality, bounded constant models, vector-space freeness/projectivity, comparison-pullback
coherence, constant-left-module exactness, coefficient-ring comparison and etale/pro-etale
cover inclusion. No proof-dependency import was omitted for a cycle.

Sources checked: local Bhatt--Scholze PDF, Proposition 6.6.11 including the forward proof,
and Proposition 6.8.11(3); local `sites-cohomology.tex`, Tag 094G,
`lemma-locally-constant`, including the full bounded constant-model induction. The present
node is the residue-field ingredient, rather than a restatement of the integral propositions.
The six-step proof docstring preserves the node's common-refinement, exactness, finite-model,
projectivity, comparison and differential-naturality steps and names their dependencies.

Edge cases checked before and after writing:

- Empty X: the finite partition can be empty; no nonempty index hypothesis occurs.
- Empty strata are allowed. The empty scheme has the empty etale cover; no nonzero P is needed.
- L = 0 and zero vector spaces: strict boundedness, finite generation and perfectness all allow zero.
- One nonzero degree: choose equal bounds; neither the hypothesis nor the conclusion requires
  a strict interval or a positive amplitude.
- Any finite field and any characteristic of X: no invertibility, characteristic inequality,
  algebraic closure, smoothness, dimension bound or finite-type-over-a-field assumption occurs.
- Nontrivial extension classes between cohomology sheaves: the theorem asks for a genuine
  constant complex locally, not a global direct-sum decomposition or merely constant homology.
- Universes: the scheme has object universe u, coefficients and module values have u+1,
  covering indices have u. No site object/Hom universe equality is imposed. A trivializing
  family can be reduced to a u-indexed subfamily by choosing a member over each point;
  the already recorded bounded-constant-model theorem uses this exact convention.

Searches (all through prescribed msearch.py plus read-only rg/grep):

- leanfinder query `A bounded constructible etale complex over a finite field admits stratified constant perfect models`: 8 hits. Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, Algebra.Etale.exists_subalgebra_fg, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, Algebra.FormallyEtale.instForallOfFinite, Algebra.Etale.iff_exists_algEquiv_prod, AlgebraicGeometry.IsEtale.of_comp, RingHom.IsStandardSmooth.exists_etale_mvPolynomial, Algebra.FormallyEtale.iff_exists_algEquiv_prod. No exact stratified finite-field complex statement.

- loogle query `"Constructible", "Perfect"`: 0 hits. . No exact stratified finite-field complex statement.

- grep query `constructible.*(perfect|complex)|stratif.*etale`: 4 hits. Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean, Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean, Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean, Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean. No exact stratified finite-field complex statement.

- leanfinder query `Bounded constructible etale complexes over finite field have perfect constant complexes after stratification`: 8 hits. AlgebraicGeometry.IsEtale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified, Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat, AlgebraicGeometry.Scheme.etaleTopology, Algebra.isOpen_etaleLocus, AlgebraicGeometry.IsEtale.of_comp, Algebra.Etale.iff_exists_algEquiv_prod, Algebra.FormallyEtale.instForallOfFinite. No exact stratified finite-field complex statement.

- loogle query `"Constructible", "Perfect"`: 0 hits. . No exact stratified finite-field complex statement.

- grep query `constructible.*(perfect|complex)|stratif.*etale`: 4 hits. Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean, Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean, Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean, Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean. No exact stratified finite-field complex statement.

- `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `stratif.*[Pp]erfect|[Ff]inite[Ff]ield.*[Mm]odel`, followed by focused finite-field and
  stratified-perfect searches: no exact theorem. AdicStratifiedPerfect is about integral
  adic coefficients; FiniteFieldLocalTensorModel is about scalar extension of a given
  local model, not existence of these strata and models.
- `grep -rn 'lem-weil-pbc-finite-field-stratified-perfect-models' lean/WeilConjectures`:
  no hits. The statement has no upstream declaration.
- `rg -n 'finite_field_stratified_perfect_models|FiniteFieldStratifiedPerfectModels'`
  on upstream name index, upstream Lean and Sheaf Lean: no hits, so the chosen name is fresh.
- Read-only search for `finiteCoefficientDerivedPullback` located the existing canonical
  finite-coefficient operation, and its complete definition and realization inverse were read.
  This avoided adding a second pullback definition or a helper node.

No STATEMENT-DISPUTED flag or mathematical node fault remains.

Validation: prescribed scompile.py on the final source passed in both sandbox and library
names, 4.4 s and 4.8 s, with no errors or warnings. The initial compile found only one
103-character line; it was wrapped before the clean compile. No Lean proof was supplied.

## Second reading by N8

Worker rereading after compilation, with the full node and final file open; independent
review is reserved for the maintainer by the dispatcher brief, and no other agent was started.
The table above checks each hypothesis and clause. In particular, the conclusion uses the
recorded finite locally closed stratification with constructibility separately imposed, each
cover is jointly surjective, finite dimensionality concerns TERMS of an actual bounded
complex, the perfectness predicate uses its recorded general localization interface, and the
identical P occurs in both constant-complex isomorphisms. The pro-etale left-hand side is
restriction of `finiteCoefficientDerivedComparison X k L` itself. Discrete-topology binders
supply the existing finite-coefficient presentation and impose no extra condition on k.
No semantic mismatch was found; the only correction during this reading was wrapping the
long line. No statement correction, new definition, or dependency interface repair was needed.
