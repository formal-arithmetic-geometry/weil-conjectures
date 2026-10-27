## Worker report

States `AlgebraicGeometry.ProEtale.directImageCTFEtaleOrigin` in
`Sheaf.Paper.SfDirectImageCTFEtaleOrigin`, with its proof wholly `sorry`.
There are no new definitions, axioms, dependency replacements, or new nodes.
The only mathematical correction makes the ordered finite-Tor interval convention
explicit; see below. The ordinary, uncompleted intrinsic constant-ring direct image
is used throughout. No completion or restriction to constructible test modules occurs.

Hypothesis-by-hypothesis correspondence:

- Global datum `(p,r,q,k₀,k)` is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its fields include primality, positive exponent, cardinality, and algebraic closure.
- The coefficient prime and its difference from characteristic are `(l : ℕ)`,
  `[Fact l.Prime]`, `_hl : l ≠ D.p`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its valuation ring and chosen uniformizer are
  exactly those in `Padic.coefficientExtensionRing l E n`, not additional choices.
- Positive quotient level is `(n : ℕ) (hn : 1 ≤ n)`.
  Coefficients on the ordinary etale site use the established `ULift.{u+1,u}`.
  `Padic.finite_coefficientExtensionRing l E n hn` and
  `Equiv.ulift.finite_iff.mpr` provide all finite-ring evidence explicitly.
  There is no additional finiteness assumption or local instance.
- `X,Y : Scheme.{u}` carry `Over (Spec (CommRingCat.of D.k))` instances.
  Each structure morphism has both `LocallyOfFiniteType` and `QuasiCompact`,
  which together mean finite type, as the recorded Mathlib dependency specifies.
- `f : X ⟶ Y` is over the same base (`f.IsOver ...`) and has precisely
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  Neither properness nor absolute separatedness of X or Y is assumed.
- Source dimension is `(d : ℕ)` and `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
- The corrected interval is `(a b : ℤ) (_hab : a ≤ b)`.
- `K' : Etale.DerivedCategoryModule (ULift ... (coefficientExtensionRing ...)) X`
  belongs to the recorded ordinary derived category on the small etale site.
- `_hK'` is exactly `Etale.DerivedCategory.isBoundedConstructible`, with the
  finite-value constructibility convention recorded on the dependency node.
- `_hTor` is the recorded `Etale.DerivedCategory.hasTorAmplitudeIn ... X a b K'`;
  every etale module sheaf in degree zero is tested.
- `K : Scheme.proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)`
  is an arbitrary object of the intrinsic constant-ring derived category.
- `_hOrigin : Nonempty (K ≅ ... K')` gives the stipulated derived isomorphism.
  The functor is the already published `finiteCoefficientIntrinsicDerivedComparison`:
  exact `comparisonUpperStar`, followed by the canonical associated-module-sheaf
  realization along the constant-scalar unit, then exact termwise derived descent.
  This is the existing intrinsic presentation of the same comparison, not an
  arbitrary chosen functor or a hypothesis that supplies one.

Clause-by-clause correspondence:

- The first conjunct supplies an etale object `L` on Y, its recorded bounded
  constructibility, and an isomorphism from its canonical comparison image to
  `(Scheme.proEtaleConstantDerivedDirectImage f A).obj K`.
  This spells out the existing essential-image definition of bounded constructible
  pro-etale objects in `def-weil-pbc-proetale-modules`, in its published intrinsic
  constant-ring coordinates. It is an existential witness, not chosen data.
- The second conjunct is exactly `Scheme.HasProEtaleTorAmplitude Y A (Rf_* K)
  a (b + 2 * (d : ℤ))`, including the interval ordering and every module test.
- The third conjunct is `WeilConjectures.finiteTorConstructible l E n hn Y (Rf_* K)`.
  This uses intrinsic finite-torsion constructibility, independently of the first
  etale-origin witness. The intrinsic/origin comparison theorem is therefore still
  a proof dependency. No identification of those notions by definition is made.

Dependency declarations and their modules were read, including docstrings:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public coefficient
  construction module): `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, with its recorded ring of integers and uniformizer.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `QuasiCompact`, `Proper`,
  `Separated`: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` and the
  separated-to-quasi-separated instance `IsSeparated.instQuasiSeparated`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: the recorded interval predicate
  is imported unchanged (this module only adds the lower-bounded variant).
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus` and the exact `Functor.mapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`,
  `finiteCoefficientDerivedComparison`, `isBoundedConstructibleFiniteCoefficient`.
  Its published coordinate conversion module
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison` supplies
  `finiteCoefficientIntrinsicRealization`, `finiteCoefficientIntrinsicComparison`,
  `finiteCoefficientIntrinsicDerivedComparison`. These canonical constructions
  represent the same module notion over the constant commutative coefficient sheaf.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports all recorded
  intrinsic ringed operations. Its existing constant-direct-image specialization in
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` is
  `Scheme.proEtaleConstantDerivedDirectImage`, the right derived functor of the
  sectionwise module direct image with the constant-section scalar map.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations` reexports
  `Scheme.HasProEtaleTorAmplitude` from `ProEtaleTorAmplitude`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` reexports
  `WeilConjectures.finiteTorConstructible` from `FiniteTorAmplitude`, using
  `Scheme.intrinsicFiniteTorsionConstructible` from
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- Proof imports: `Sheaf.Paper.SfDirectImageCTFNonproper` (`Etale.directImageCTFNonproper`),
  `Sheaf.AlgebraicGeometry.ComparisonDirectImage` (`isIso_comparisonDirectImagePlus`),
  `Sheaf.AlgebraicGeometry.ComparisonTorInterval` (`comparison_torAmplitudeIn_iff`),
  `Sheaf.Paper.ProEtaleConstructibleOrigin` (`constructible_proEtale_origin`).
  All already stated proof dependencies are imported; no import cycle was introduced.

Edge cases checked: K'=K=0; the empty scheme (dimension bottom); d=0; a=b;
negative endpoints; identity morphisms; n=1. Level n=0 is excluded by the source.
No source-separation hypothesis is imposed on structure maps. No relation equates
site object and morphism universes: the small sites retain object universe u+1 and
morphism universe u, and module values use u+1. The zero object with a>b exposed
an actual inherited node fault, which is corrected below, rather than silently dropped.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Derived direct image preserves bounded constructible
  etale origin and Tor amplitude on pro etale sites"`: eight results, basic etale
  site declarations only, no matching statement.
- `msearch.py ... loogle "AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible,
  AlgebraicGeometry.ProEtale.lowerStar"`: zero hits, unknown identifier in that index.
- `msearch.py ... grep "boundedConstructible.*rightDerivedLowerStar|directImageCTF"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for direct-image CTF and etale-origin
  names, plus `grep -rn` for the item id, found upstream
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability` and the
  existing direct-image amplitude modules. The upstream theorem
  `boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory`
  was opened in full. It uses arbitrary field/annihilator coefficients, the literal
  comparison image as input, and etale-origin constructibility as its output. It
  does not have this item's full signature: arbitrary isomorphic intrinsic K,
  the finite-field/extension quotient specialization, and the separate intrinsic
  Dctf conclusion. It supplies useful proof material but is not an exact existing
  statement match. No existing notion has been defined again in this delivery.

Validation: `scompile.py Q30 cor-sf-direct-image-ctf-etale-origin <module>` passed
both sandbox and library-name compilation, each in 3.9 seconds, with no diagnostics.

## Statement corrected

The original statement is preserved verbatim in `statement_change.old_statement`.
The exact changed phrase is `Let $a,b$ be integers and let` to
`Let $a\leq b$ be integers and let`; all other objects, hypotheses and conclusions
are unchanged. The fourth proof step now uses a<=b directly, removing only its
incorrect empty-interval branch. `old_proof` preserves the complete original proof.

Reason: the original etale input predicate allows an empty interval, but the cited
pro-etale output predicate explicitly includes a<=b. On X=Y=Spec(k), f=id, d=0,
a=1, b=0, K'=K=0, every original hypothesis holds and the conclusion contains
1<=0. The source speaks of finite Tor amplitude in an interval; both its cited
`def-weil-proetale-tor-amplitude` and `def-weil-finite-tor-amplitude` require ordered
endpoints. The correction makes this existing convention explicit. Source:
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-cor-sf-direct-image-ctf/`
`cor-sf-direct-image-ctf-etale-origin.md`, finite-Tor interval clause, read with those
ordered definitions. The item is not the unit's key statement; the unit statement
is unchanged.

Complete current citer audit (scanned every node's stmt_deps and proof_deps):

- `lem-sf-completed-projection-exchange-realization`: holds. Its finite-level
  constructible finite-Tor bounds are ordered intervals, including after taking
  finite minima and maxima; it can supply this convention at every application.

`cor-sf-direct-image-ctf-proetale` is also a textual/blueprint citer but is not a
current stmt_deps/proof_deps citer. Its current proof directly assembles the etale
and comparison results, and its intrinsic Tor input already forces ordered endpoints.
No citer is edited. No unresolved statement dispute remains after the correction.

## Second reading by Q30

Reopened the node, its source and proof, all dependency records, and the completed
module. The dispatcher explicitly prohibits spawning another agent; this section
records the worker's second pass, with independent review left to the maintainer.
Checked every binder and all three conclusions against the corrected statement as
mapped above. The mismatch found was the empty-interval condition and was repaired
with the complete statement_change record. In particular, the final intrinsic Dctf
clause was checked independently of the etale-origin witness, avoiding the inherited
proof's earlier constructibility conflation. The existential witness is a membership
condition, not construction by a bare existence choice. The same canonical ordinary
Rf_* appears in every conclusion. Proof finiteness is supplied explicitly rather
than imposed as an additional assumption. No further mismatch was found.
