## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeComposition` states
`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfDegree_comp`. Its only theorem
has a `sorry` proof, with the complete five-step DAG proof in its docstring.
There are no new definitions, dependency repairs, statement corrections or disputed
statements. The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- Schemes `X,Y,S`: `{X Y S : Scheme.{u}}`, with arbitrary explicit universe `u`.
- Integers `r,s ≥ 0`: `(r s : ℕ)`, the same natural degree parameter used by the
  dependency definition; zero is included.
- Morphisms `f : X → Y` and `g : Y → S`: `(f : X ⟶ Y) (g : Y ⟶ S)`.
- Finite local freeness and constant degrees `r,s`:
  `[f.IsFiniteLocallyFreeOfDegree r] [g.IsFiniteLocallyFreeOfDegree s]`.
  The dependency class extends `IsFiniteLocallyFree`, which in turn extends
  `IsFinite`, `Flat` and `LocallyOfFinitePresentation`. Its field
  `fiberDegree_eq (s : S) : f.fiberDegree s = d` asserts exactly the dimension
  of global sections of the scheme-theoretic fibre over the residue field.
- Composite `g ∘ f`: `f ≫ g`, in diagrammatic composition order.
- Finite local freeness and constant degree `rs` of the composite:
  `(f ≫ g).IsFiniteLocallyFreeOfDegree (r * s)`.
- Absence of reducedness, Noetherianity, connectedness and separability hypotheses:
  none of these classes or assumptions occurs in the signature.
- Empty schemes and zero degree: no `Nonempty`, `Nontrivial`, positive-degree,
  surjectivity or integral-scheme hypothesis occurs.

Statement dependency declarations were read with their full signatures and docstrings:
`Mathlib.AlgebraicGeometry.Scheme`, declarations `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom`; and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, declarations
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` (including its
`fiberDegree_eq` field). Both owning modules are public imports. The withdrawn
CompactObject example was checked together with its node's current upstream
binding, and the upstream module-mode convention is followed.

Proof dependency imports follow the recorded interfaces:

- `lem-trf-finite-locally-free-composition`: the finite, flat and locally
  finite-presentation stability instances from Mathlib's `Morphisms.Finite`,
  `Morphisms.Flat` and `Morphisms.FinitePresentation`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`, supplied by
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `lem-weil-pbc-fibre-product-affine-spectra`: `AlgebraicGeometry.pullbackSpecIso`,
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `lem-a1-finite-locally-free-principal-basis-cover`:
  `AlgebraicGeometry.finiteLocallyFree_principalBasisCover`,
  `Sheaf.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover`.
- `def-weil-module-base-change`: `LinearMap.baseChange`,
  `Mathlib.LinearAlgebra.TensorProduct.Tower`.
- `def-weil-pbc-module-localization-away`: `LocalizedModule.Away`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`.
- `lem-weil-pbc-finite-dim-algebra-artinian` and `lem-sfb-artinian-spectrum-finite`:
  `IsArtinianRing.of_finite` and `IsArtinianRing.setOfPred_isPrime_finite`,
  `Mathlib.RingTheory.Artinian.Module`.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`.
- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`.

`lem-sfb-semilocal-constant-rank-basis` has no recorded Lean interface and hence
no module to import yet; it is used only in the postponed proof, not in the
statement. It remains explicitly named in the proof docstring. All other proof
nodes with recorded modules or Mathlib matches are imported. No new prerequisite
is needed to type the statement.

Sources checked: Stacks `morphisms.tex`, definitions/lemmas with labels
`definition-finite-locally-free`, `lemma-finite-flat`,
`lemma-composition-finite-locally-free` (Tags 02KA, 02KB, 02KC), and
`algebra.tex`, `lemma-locally-free-semi-local-free` (Tag 02M9).
The actual finite-locally-free definition uses pushforward local freeness;
02KB establishes equivalence with the dependency class's finite/flat/lfp form.

Edge cases checked before writing: an empty base makes all degree conditions
vacuous and forces all source schemes empty, so arbitrary `r,s` cause no issue;
`r = 0` gives zero source fibres; `s = 0` gives empty intermediate fibres and
zero composite fibres. Over an empty intermediate scheme the degree of `f`
may be arbitrary, but the product with the degree-zero `g` is still zero.
Nonreduced finite fibre algebras are retained: dimension is dimension of the
whole algebra, not a count of geometric points or a separable degree.
Disconnected bases are allowed because the hypotheses require constant rank
at every point. A single scheme universe imposes no mathematical restriction:
all three schemes of any fixed finite diagram lie in a common universe.

Searches for an existing statement (all via the prescribed msearch wrapper):

- LeanFinder: “The composite of finite locally free scheme morphisms of constant
  degrees r and s is finite locally free of degree r times s”. Eight hits on
  composition of finite or locally finite type/quasifinite morphisms; no degree
  statement.
- Loogle: `AlgebraicGeometry.Scheme.Hom.finrank`. Twelve hits: the rank function,
  base-change formula, isomorphism formulas and affine rank comparison; no
  constant-degree composition theorem.
- Mathlib grep: `finrank_comp|degree_comp|IsFiniteLocallyFree`, in
  `AlgebraicGeometry`. Five hits in `Morphisms/FlatRank.lean`, concerning
  isomorphisms; no match.
- LeanSearch: “The composition of finite locally free morphisms of constant
  degree r and s has constant degree r times s”. Eight hits on polynomial
  degrees and finite-morphism composition, no match.
- Project and upstream `rg`:
  `finrank_comp|degree_comp|FiniteLocallyFree.*(comp|degree)|finiteLocallyFree.*(comp|degree)`;
  and search for the exact node id in `WeilConjectures`. No exact node-id hit.
  The conceptual search found
  `AlgebraicGeometry.Scheme.Hom.finrank_comp_of_forall_finrank_eq` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatRank`. Its full
  statement and proof were read: it asserts a pointwise `finrank` identity for
  finite flat maps, with only the first map of constant rank. It does not
  conclude `IsFiniteLocallyFreeOfDegree`, so cannot be recorded as an exact
  existing conclusion under the rule for more general existing theorems.
  The present statement reuses the existing definition rather than introducing
  a rank or degree notion. An additional search for `IsFiniteLocallyFreeOfDegree`
  in both project trees found applications and the original class, no matching
  composition declaration.

Validation: the delivered module is checked with the prescribed `scompile.py`,
followed by `deliver2.py --no-push` and `deliver2.py`. The only expected compiler
warning is the theorem's postponed `sorry` proof.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
