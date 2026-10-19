## Worker report

The delivery states `AlgebraicGeometry.Etale.finiteStage_directImage_torAmplitude` in
`Sheaf.Paper.FiniteStageDirectImageTorAmplitude`. Its only proof is `sorry`. No definitions,
new nodes, dependency repairs, or statement corrections are needed. The item node changes
only in `lean`; the current Q59 stage-1 split, its seven proof steps and its review are retained.
The previous unchanged-node rejection is resolved by supplying the previously absent Lean
attachment and its module, rather than resubmitting the stage-1 split.

Source read: main-20261015, sec-six-functors-basics,
`sk-thm-sf-direct-image-tor-amplitude/_section.md`, order 1712, together with the item's
seven-step proof and the standing definitions. The statement is unchanged.

Hypotheses and conclusions, clause by clause:

- The standing prime p, positive exponent, q = p^exponent, finite field k0 and its fixed
  algebraic closure k are `D : WeilConjectures.FiniteFieldDatum.{u}`. In particular
  `D.k` is the standing field; the datum's cardinality and prime-power fields imply
  characteristic `D.p` for k0 and its algebraic closure.
- The coefficient prime and its inequality are `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The finite extension E/Q_l is `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its valuation ring and chosen uniformizer are those
  used by the recorded `Padic.coefficientExtensionRing`, not separately chosen data.
- The positive coefficient level is `(n : ℕ) (hn : 1 ≤ n)`. Every occurrence of the
  coefficient ring is exactly `Padic.coefficientExtensionRing l E n`, the quotient of
  the recorded integer ring by the nth power of its uniformizer ideal. The required
  `Finite` instance is explicitly `Padic.finite_coefficientExtensionRing l E n hn`;
  finiteness is not an extra hypothesis.
- The k-schemes are `{X Y : Scheme.{u}}` with `[X.Over (Spec (.of D.k))]` and the
  corresponding instance for Y. Finite type over k is the pair `LocallyOfFiniteType`
  and `QuasiCompact` on each structure morphism `X ↘ Spec (.of D.k)` and similarly Y.
- The morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]`. Its separated finite-type
  hypotheses are `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
- The source dimension bound is `(d : ℕ)` and
  `(_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))`.
- The endpoints are arbitrary `(a b : ℤ)`; no ordering hypothesis is added.
- The complex is `K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X`.
  This is the ordinary derived category of `Sheaf X.smallEtaleTopology (ModuleCat A)`.
  `_hK : @DerivedCategory.isBoundedConstructible ... X K` states both boundedness and
  constructibility using exactly the recorded dependency predicate.
- `_hTor : DerivedCategory.hasTorAmplitudeIn ... X a b K` tests all degree-zero module
  sheaves and vanishing in each degree outside `[a,b]`, exactly as def-kun-tor-amplitude.
- The first conclusion is `@DerivedCategory.isBoundedConstructible ... Y (Rf.obj K)`.
  The second is `DerivedCategory.hasTorAmplitudeIn ... Y a (b + 2 * (d : ℤ)) (Rf.obj K)`.
  Their conjunction asserts both clauses with exactly the required upper shift.
- Here `Rf` is `rightDerivedLowerStar (ModuleCat.{u + 1} A) f`, the named unbounded
  right derived functor of the recorded `lowerStar`, defined as its
  `rightDerivedFunctor`. On the bounded-below inputs in this node it computes the same
  Q(f_*I) as the recorded `rightDerivedLowerStarPlus`. No arbitrary direct-image map
  or alternative tensor construction occurs.

Recorded dependency declarations read and used:

| Node | Module | Declaration(s) used |
| --- | --- | --- |
| def-weil-finite-field-fiber | Sheaf.Paper.FiniteFieldFiber | WeilConjectures.FiniteFieldDatum |
| def-weil-l-adic-coefficient-extension | Sheaf.NumberTheory.Padics.CoefficientExtensionFinite, importing Sheaf.NumberTheory.Padics.CoefficientExtension | Padic.coefficientExtensionRing; Padic.finite_coefficientExtensionRing |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact | AlgebraicGeometry.LocallyOfFiniteType; AlgebraicGeometry.QuasiCompact |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper; Mathlib.AlgebraicGeometry.Morphisms.Separated | AlgebraicGeometry.IsSeparated |
| def-weil-pbc-constructible-complexes | WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes | AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible |
| def-kun-tor-amplitude | Sheaf.AlgebraicGeometry.EtaleTorAmplitude; WeilConjectures.SixFunctors.Etale.Derived.Coefficients | AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn |
| def-weil-pbc-derived-categories | WeilConjectures.AlgebraicGeometry.DerivedCategories; WeilConjectures.SixFunctors.Etale.Derived.Coefficients | AlgebraicGeometry.Etale.DerivedCategoryModule |
| def-weil-pbc-direct-image | WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs; WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence | AlgebraicGeometry.Etale.lowerStar; rightDerivedLowerStar; rightDerivedLowerStarPlus |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension | topologicalKrullDim |

The current upstream bounded-constructible and derived-category source modules were read
through `scompile.py --source`, since their recorded upstream versions are absent in the
older local checkout. The current upstream `Derived.Stability.DirectImage` was also read
through that wrapper. All already-stated proof-dependency modules are imported privately:
Tensor, LowerStarProjection, DirectImageVanishing, ResidueTorAmplitudeTest,
EtaleDirectImageVanishing, FiniteConstantProjectionFormula, ExtensionIntegersDvr,
EtaleConstantModuleDirectImageLeftExact, EtaleModuleSheavesGrothendieckAbelian,
Mathlib.Topology.Algebra.Valued.LocallyCompact, FiniteTypeDirectImageConstructibility and
WeilConjectures.CategoryTheory.TruncationHypercohomology. Public imports expose the
statement's definitions. The theorem docstring records the seven current proof steps and
their DAG dependencies. No proof import is omitted for a cycle.

Edge cases checked before writing:

- Empty X has dimension bottom, so its dimension bound is admitted for every d; its
  zero derived direct image satisfies the conclusion. Empty Y also forces empty X.
- K = 0 is admitted for every pair of endpoints, including `a > b`. The interval Tor
  predicate deliberately supports empty intervals; no hidden `a ≤ b` hypothesis occurs.
- d = 0 gives upper endpoint b, without an extra shift. For an identity map and a
  shifted constant coefficient complex the original interval remains admitted.
- For the projective line with constant coefficients and d = 1, degree-two cohomology
  explains the exact positive upper shift 2 rather than a negative shift.
- n = 1 is included, and n > 1 does not require the residue field to have finite
  projective dimension. The proof uses the finitely presented constant projection
  formula, not a perfect-residue-field assumption. n = 0 is excluded by the source.
- The coefficient field is allowed in `Type (u+1)` so the coefficient ring directly
  has the size required by the recorded etale module-sheaf API; no equality of site
  object and morphism universes is imposed. Finite extensions may be represented in
  that universe, including universe lifts of smaller presentations. All universes
  and variables are explicitly bound, with `autoImplicit false` in the delivered file.
- No properness, compactification, smoothness, or flatness of K is assumed.

Searches made (2026-10-17):

1. `msearch.py leanfinder`, query `derived direct image bounded constructible etale complex
   finite Tor amplitude interval shift twice source dimension`: eight generic derived
   category support/single-functor/truncation results; no exact theorem.
2. `msearch.py loogle`, query `CategoryTheory.Functor.rightDerived`: twelve abstract
   derived-functor results, with no constructible direct-image Tor bound.
3. `msearch.py grep`, query `hasTorAmplitudeIn|isBoundedConstructible`, scope `Algebra`:
   zero Mathlib hits.
4. `msearch.py leansearch`, query `derived direct image of a bounded constructible etale
   complex has finite Tor amplitude with interval upper bound shifted by twice source
   dimension`: eight generic fraction, t-structure, shift and exact-functor results;
   no exact theorem.
5. `rg` in upstream WeilConjectures and project lean/Sheaf, queries
   `sk-thm-sf-direct-image-tor-amplitude|isBoundedConstructible.*[Dd]irect|hasTorAmplitudeIn.*[Dd]irect`,
   and literal `grep -rn` for the item id in the upstream source: found upstream
   DirectImage and references to it, plus the older project corollary. Read their full
   signatures and docstrings. Neither upstream result uses the recorded
   `isBoundedConstructible` predicate; the generic upstream Tor theorem also uses the
   distinct generic `torAmplitudeIn` predicate. The project `directImageCTFNonproper`
   likewise uses `boundedConstructible`, whose difference is explicitly documented in
   the recorded constructibility dependency. These are not exact reusable attachments
   for this node's recorded definitions. `sf_directImage_torAmplitude` uses the right
   predicate but assumes a separate UDV bound and `a ≤ b`, so does not state this item.
6. `rg` for `finiteStage_directImage_torAmplitude|finiteStage.*[Dd]irect|isBoundedConstructible.*rightDerivedLowerStar`
   in the upstream and project roots: no collision for the new declaration; related
   proper, open, finite and general constructibility results have no Tor conclusion.

Validation: `scompile.py Q117 sk-thm-sf-direct-image-tor-amplitude` compiled the delivered
module both as sandbox and module path, cleanly (3.1 s and 4.0 s). One diagnosed import
visibility error was fixed by publicly importing UpperLowerStarCoherence, which owns
rightDerivedLowerStar. There are no remaining warnings or errors. The only postponed
proof is the named theorem matching this item. No STATEMENT-DISPUTED issue was found.

## Second reading by Q117

I independently read the sandbox node and module against main-20261015,
`sec-six-functors-basics/sk-thm-sf-direct-image-tor-amplitude/_section.md`, order 1712,
its proof file, and the chapter introduction. This is the ordinary finite-coefficient
étale assertion, despite the surrounding chapter's additional pro-étale layers.
The source place of this item is a blueprint file, not a Stacks tag. Its explicit
standing conventions in the node agree with the finite-field and coefficient nodes.
No statement correction, new definition node, or dependency module is needed.

The inventory below matches every object, hypothesis, and conclusion. In the last
three entries, `A` abbreviates `Padic.coefficientExtensionRing l E n` in this report
only; there is no extra abbreviation or local notation in the Lean module.

| Source item | Lean rendering and verdict |
| --- | --- |
| Standing prime p, positive exponent, finite field of cardinality q = p^exponent, fixed algebraic closure k | `D : WeilConjectures.FiniteFieldDatum.{u}`. Read its structure fields, registered field instances and `IsAlgClosure` instance. Correct: k is `D.k`, not an arbitrary field or a finite field. |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. Correct, including p = 2 and ell = 2 when distinct. |
| Finite extension E/Q_ell | `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Correct; no unrequested norm, topology, or completeness hypothesis is imposed. |
| Valuation ring, chosen uniformizer, A = O_E/(uniformizer^n), n at least 1 | `(n : ℕ) (hn : 1 ≤ n)` and `Padic.coefficientExtensionRing l E n`. Read CoefficientExtension and CoefficientExtensionFinite: the absolute value is the spectral extension, the integer ring has its prescribed membership characterization, and the quotient ideal is the nth power of the chosen uniformizer ideal. Correct reuse of the dependency. The explicit `finite_coefficientExtensionRing ... hn` is a theorem, not an extra finiteness assumption. |
| Finite-type k-schemes X and Y | `{X Y : Scheme.{u}}`, their `Over (Spec (.of D.k))` instances, and `LocallyOfFiniteType` plus `QuasiCompact` for each structure map. Correct; neither scheme is assumed separated over k. |
| A separated finite-type morphism f over k | `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. Correct: the over instance gives compatibility of structure maps, and IsSeparated means closed diagonal. No properness or compactification is assumed. |
| Natural dimension bound d with dim X at most d | `(d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))`. Correct; read Mathlib's definition as the Krull dimension of irreducible closed subsets. |
| Integer endpoints a,b | `(a b : ℤ)`. Correct; the source does not assume `a ≤ b`, and the module does not add it. |
| Ordinary A-module-sheaf derived complex K on the small étale site | `(K : DerivedCategoryModule A X)`. Read Coefficients and the current DerivedCategories module: this expands to `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))`. Correct category and coefficient ring. |
| Bounded constructibility of K | `_hK : @DerivedCategory.isBoundedConstructible A _ (Padic.finite_coefficientExtensionRing ... hn) X K`. Read the current BoundedConstructibleComplexes source through `scompile.py --source`: all cohomology sheaves satisfy the recorded finite-constant-module constructibility predicate and vanish outside some bounded interval. Correct dependency, rather than the distinct older `boundedConstructible`. |
| Tor amplitude [a,b] of K | `_hTor : DerivedCategory.hasTorAmplitudeIn A X a b K`. Read its full definition in Coefficients and the recorded EtaleTorAmplitude module: every degree-zero module sheaf is tested, with zero cohomology for `q < a ∨ b < q`. Correct; neither only constant sheaves nor only flat/perfect test objects are used. |
| The derived direct image Rf_*K | `(rightDerivedLowerStar (ModuleCat.{u+1} A) f).obj K`. Read lowerStar and UpperLowerStarCoherence: lowerStar is precomposition along étale base change, and this is its total right derived functor. Correct module direct image; on the bounded-below input it agrees with the dependency's bounded-below functor computed by Q(f_*I). |
| Rf_*K is bounded constructible | First conjunct uses the very same `@DerivedCategory.isBoundedConstructible A ...`, now at Y and the above image. Correct, with no conclusion omitted. |
| Rf_*K has Tor amplitude [a,b+2d] | Second conjunct is `DerivedCategory.hasTorAmplitudeIn A Y a (b + 2 * (d : ℤ))` of the same image. Correct sign, coefficient ring, quantifier order, and exact upper endpoint. |

Edge cases: empty X has dimension bottom and is admitted for every d; empty Y
forces empty X. Zero K is allowed, including empty intervals a > b. When a > b,
the Tor condition tested on the tensor unit forces K to be zero, so no ordering
assumption is needed. d = 0 leaves the upper endpoint b. n = 1 is included and n = 0
is excluded exactly as in the source. For n > 1 no perfection of the residue field
is assumed. The bound uses source dimension, with the positive shift 2d (as for
cohomology of the projective line). The universe u is arbitrary; E and module values
are in u+1, the size of the recorded ordinary étale API. Finite-dimensional p-adic
extensions can be represented there, including lifts of smaller presentations. No
independent site universes have been equated and no index family is restricted.

Independent searches used different wording from the first worker:

- `msearch.py ... leanfinder "finite coefficient etale pushforward preserves constructibility and tensor amplitude with dimension bound"`: eight results on étale algebras and morphisms, no match.
- `msearch.py ... leansearch "pushforward of constructible complexes finite Tor dimension cohomological amplitude etale sheaves"`: eight ordinary sheaf/presheaf/module pushforward results, no match.
- Loogle `CategoryTheory.Functor.rightDerivedFunctor` was an unknown identifier in the search index and is inconclusive. The valid follow-up `CategoryTheory.Functor.rightDerived` returned twelve abstract right-derived-functor results and no target statement.
- Direct `rg` of Mathlib's AlgebraicGeometry, CategoryTheory, and Algebra/Homology trees for `TorAmplitude|torAmplitude|tor_amplitude|[Cc]onstructible.*[Pp]ushforward|[Cc]onstructible.*[Dd]erived` found no match.
- Direct `rg` of upstream WeilConjectures and project lean/Sheaf found the upstream Stability.DirectImage results, `directImageCTFNonproper`, and `sf_directImage_torAmplitude`. I opened their declarations. The first two use the distinct `boundedConstructible`; the upstream generic Tor result uses `torAmplitudeIn`. The last uses the correct predicates but assumes UDV and a ≤ b instead of the dimension bound. None supplies this node's exact statement. The new declaration name has no collision in either root.

H4/H12/H13: all nine statement-dependency records were read, together with the
signatures and bodies of the definitions used. No private construction, new node,
or replacement dependency is present. The recorded current bounded-constructibility
and derived-category modules were fetched with the authorized source wrapper. The
Mathlib finite-type, quasi-compact, separatedness and dimension interfaces were read
directly. Existing nearby declarations are not substituted for different predicates.

H5/H6/H8/H9: the delivery contains exactly one theorem, with whole proof `sorry`;
there are no definitions or auxiliary proved facts. The source and blueprint tags
are in both docstrings. The theorem docstring follows all seven DAG steps: coefficient
arithmetic; residue-tensor concentration and lower truncation; truncation spectral
sequence; all-module vanishing and filtration; constructibility; finite-presentation
projection formula and compatibility of direct images; residue Tor test. The stated
proof-dependency modules are imported. No line exceeds 100 characters, and all
variables/universes are bound explicitly. The node's `lean.statement` is byte-for-byte
equal to the theorem signature before `:= by`.

Mismatches and changes: no mathematical or interface mismatch was found; the Lean
module and node record are retained unchanged. Only this independent second-reading
section was appended. Validation results follow below.

Second-reader validation: `scompile.py Q117 sk-thm-sf-direct-image-tor-amplitude`
with the absolute delivered file path compiled the sandbox (2.9 s) and module (3.2 s)
cleanly, with no diagnostics. An initial invocation from the read-only repository
with a sandbox-relative filename failed to locate the input before compilation;
rerunning with its absolute sandbox path resolved that invocation error.
