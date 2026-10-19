## Worker report

The new module `Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness` states
`AlgebraicGeometry.Etale.finiteType_directImages_finiteConstructible`, with its entire
proof `sorry`. It retains the node's three assertions in one conjunction, and its
docstring gives the five-step proof plan. No definition or auxiliary theorem is introduced.
The node's natural-language statement and proof are unchanged.

Hypotheses and conclusions, clause by clause:

- A field: `(k : Type u) [Field k]`.
- Finite commutative prime-to-characteristic coefficients: `(Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ]`, with `(N : ℕ)` and
  `hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`. This is precisely the
  recorded coefficient convention: positive N, a finite ring killed by N, and N a unit
  on Spec k. It adds no characteristic-zero or nonzero-ring restriction.
- Finite-type schemes over k: `(X Y : Scheme.{u})`, the two `Over (Spec (.of k))`
  instances, and `LocallyOfFiniteType` and `QuasiCompact` on their structural maps.
- A finite-type k-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`,
  `[LocallyOfFiniteType f] [QuasiCompact f]`.
- The finite constructible sheaf: `F : Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)` and `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
  This recorded notion uses a finite locally closed constructible stratification with
  finite constant module values on etale trivializations; thus it includes finite stalks.
  There is no separate global finiteness-of-sections condition.
- `Ru_* F` bounded constructible: the first conjunct is
  `DerivedCategory.isBoundedConstructible Λ Y` applied to
  `rightDerivedLowerStar (ModuleCat Λ) f` on `DerivedCategory.singleFunctor _ 0` of F.
- Separatedness is conditional: `∀ [IsSeparated f], ...` follows the first conjunct.
  Thus the ordinary-image assertion includes nonseparated morphisms.
- `Ru_! F` bounded constructible: the next conjunct uses the same predicate and degree-zero
  input, with `rightDerivedLowerShriekOfCompactification (ModuleCat Λ)
  (compactSupportAmplitudeCompactification k Y f)`. The helper is the already-defined
  Nagata compactification, supplying the Noetherian and quasi-compact base instances from
  finite type over k. No additional compactification assumption is made. On F[0], the
  bounded-below comparisons identify this candidate with compactification-independent Ru_!.
- If the geometric fibres have dimension at most d: `∀ (d : ℕ), (∀ y : Y, ... ≤ d) → ...`.
  The displayed fibre is the actual scheme pullback along
  `Spec (AlgebraicClosure (Y.residueField y)) ⟶ Y`, and dimension is `topologicalKrullDim`.
  It bounds the original f, never the proper map of the compactification.
- `R^q u_! F = 0` for q > 2d: `∀ (q : ℤ), 2 * (d : ℤ) < q → IsZero ...`, with
  `DerivedCategory.homologyFunctor` in degree q on exactly the compact-support object above.
  There is no amplitude assertion for ordinary direct image.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`. The recorded bounded-below derived declaration lives
  in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`; its unbounded companion
  `rightDerivedLowerStar` is used on the bounded-below degree-zero input, as in the
  already-stated general finite-type constructibility theorem. The generic derived-functor
  construction and compatibility supply the ordinary unbounded interpretation.
- `def-weil-pbc-scheme-conventions` has a convention-only record, with no declaration;
  its Mathlib `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` are reused.
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the imported `DerivedCategoryModule`,
  `DerivedCategory.singleFunctor`, and `DerivedCategory.homologyFunctor`, with the recorded
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` coefficient category.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim : WithBot ℕ∞`.
- The already-stated proof dependency `lem-dg-compact-support-amplitude` supplies
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude`:
  `AlgebraicGeometry.Etale.compactSupportAmplitudeCompactification`. Its exact declaration
  and docstring were read. Its node ID is additionally listed in `stmt_deps` because this
  helper occurs in the statement; this is the authorized addition of an already-landed node
  under brief-stage2 section 5. No dependency node is restated or modified.

All stated proof-dependency modules are imported; proof-only modules use private `import`.
The two Noetherian lemmas are Mathlib matches in `Mathlib.AlgebraicGeometry.Noetherian`
and the quasi-compact morphism API. The general finite-type constructibility, proper
bounded-constructibility and compact-support amplitude modules were read, including full
signatures and proof docstrings. The compactification and comparison modules are imported
for the remaining proof steps. The theorem itself asserts no new comparison equality.

Edge cases checked before writing:

- The zero sheaf and empty X are admitted; no `Nonempty`, nonzero-stalk or positive-dimension
  hypothesis is imposed. Empty geometric fibres have dimension bottom and satisfy every
  natural dimension bound. Empty Y is admitted too (then a morphism to it has empty source).
- d = 0 gives vanishing in every positive degree, with the strict inequality as stated.
  q = 2d is not claimed to vanish. No fibre-bound condition occurs in either finiteness clause.
- The zero coefficient ring is admitted. N = 1 works for it; its exponent is 1.
  Positive characteristic is handled by invertibility of N; characteristic zero requires
  no additional coefficient restriction.
- Separatedness is not assumed for the first clause. No properness assumption is imposed
  on f in any clause. No dimension bound is imposed on the compactification.
- The universe convention is the recorded small-etale module-sheaf encoding: schemes and k
  in universe u, coefficient ring and module values in u+1. No independent smaller universe
  of geometric test fields can make a hypothesis vacuous: use each actual residue-field
  algebraic closure. The chosen closure is the same construction as the amplitude dependency.

Searches for an existing exact statement:

1. `msearch.py ... leanfinder "finite type morphism schemes over field derived pushforward
   finite constructible etale sheaf bounded constructible compact support vanishing"`:
   8 hits, concerning finite morphisms/fibres, locally finite type, quasi-finiteness and
   constructible images of subsets; none states this sheaf theorem.
2. `msearch.py ... loogle '"constructible", "Sheaf"'`: 0 hits.
3. `msearch.py ... grep 'rightDerivedLowerStar|rightDerivedLowerShriek|
   IsConstructibleEtaleModuleSheaf' AlgebraicGeometry`: 0 Mathlib hits.
4. `msearch.py ... leansearch "finite type direct image of constructible etale sheaves
   bounded constructible"`: 8 hits on finite-type sheaves of modules, finite presheaves,
   and sheaf images; none gives etale direct-image finiteness or compact-support amplitude.
5. `rg -n 'sbc-thm-finiteness-finite-type|finiteness_finiteType|
   finiteType.*constructible|finiteType_construct'` in upstream `WeilConjectures` and
   project `lean/Sheaf`: found upstream
   `SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`, which was opened and read.
   Its explicitly tagged theorem states only the vanishing clause and uses upstream
   `Scheme.IsConstructibleSheaf` (finite generation of geometric stalks), rather than
   the project's finite-constant-value stratification predicate. Its other general
   finiteness theorems likewise use upstream `DerivedCategory.boundedConstructible`.
   They are not an exact existing declaration of this node with its recorded notions.
   The two relevant project constructibility theorems are proof dependencies, not duplicate
   declarations of this three-clause sheaf statement.
6. Searched the proposed full declaration name in Mathlib, upstream and `lean/Sheaf`:
   no existing occurrence. Searched `dag/lean_names_upstream.json` for the blueprint ID:
   no match. Direct source searches found the tagged upstream partial statement above.

No disputed statement, missing prerequisite, source correction, new node, or dependency
module is needed. The source blueprint markdown was opened and agrees verbatim with
this node's statement. In particular it explicitly retains nonseparated ordinary image
and specifies the original fibres for the compact-support bound.

Validation: `scompile.py` compiled the final file cleanly (no warnings or errors).
`deliver2.py Q34 sbc-thm-finiteness-finite-type --no-push` printed OK: the commit
compiles and passes preflight except for the independent second-reading section, which
the second reader must write. Nothing was pushed. No global build or direct Git command
was run.

## Second reading by Q34

I independently read the repository node, the sandbox node and the complete Lean module,
with the source blueprint markdown
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/`
`sbc-thm-finiteness-finite-type.md` open. This item's source is that blueprint,
not a Stacks lemma with additional standing hypotheses. The markdown states the three
clauses verbatim and explicitly includes the nonseparated ordinary-image case and the
bound on the original geometric fibres. There is no statement correction to audit.

Object/hypothesis/conclusion checklist, in source order:

1. A field and finite-type schemes over it: `k : Type u`, `[Field k]`,
   `X Y : Scheme.{u}`, their `Over (Spec (.of k))` instances, and
   `LocallyOfFiniteType` plus `QuasiCompact` on both structural morphisms. These
   are precisely the recorded finite-type convention, without separatedness or
   properness of either structural morphism. Verdict: matches.
2. A finite-type morphism over that field: `f : X ⟶ Y`,
   `[f.IsOver (Spec (.of k))]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`.
   The compatibility instance identifies the two structural morphisms under f, as
   in the finite-type direct-image dependency's explicit `hf : f ≫ aY = aX`.
   There is no `[IsSeparated f]` among the hypotheses for ordinary image.
   Verdict: matches the source's morphism of finite-type schemes over a field.
3. Finite commutative prime-to-characteristic coefficients: `Λ : Type (u + 1)`,
   `[CommRing Λ]`, `[Finite Λ]`, `N : ℕ` and
   `hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`.
   I opened this definition: its body is exactly `0 < N ∧ Finite Λ ∧
   (N : Λ) = 0 ∧ IsUnit (N : Γ(Spec (.of k), ⊤))`. This expresses the
   coefficient convention on the field, without a characteristic-zero, field-coefficient,
   nonzero-ring or invertibility-on-an-unrelated-base assumption. Verdict: matches.
4. A finite constructible sheaf F: `F : Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)` and `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
   I opened `IsConstructibleEtaleModuleSheaf` and its `LocallyClosedStratification`:
   a finite partition by locally closed constructible parts, realized by scheme
   immersions, whose inverse-image sheaves have etale trivializations with finite
   constant module values. This is the recorded notion, not merely finite generation
   of arbitrary geometric stalks. No finite global-section condition is imposed.
   Verdict: matches.
5. `Ru_*F` is bounded constructible: the first conjunct applies
   `DerivedCategory.isBoundedConstructible Λ Y` to
   `(rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).obj` of F placed in degree zero
   by `DerivedCategory.singleFunctor _ 0`. I opened the bounded-constructible
   predicate: every integer-degree cohomology sheaf has the predicate from item 4,
   and all cohomology outside some integer interval `[a,b]` is zero.
   I also read `rightDerivedLowerStar` in `UpperLowerStarCoherence`: it is the
   total right derived ordinary direct image, on the same unbounded category.
   Verdict: matches, including the nonseparated case.
6. If f is separated, `Ru_!F` is bounded constructible: `∀ [IsSeparated f],`
   guards the second conjunct and the subsequent amplitude assertion only.
   The compact-support object is `rightDerivedLowerShriekOfCompactification`
   on `compactSupportAmplitudeCompactification k Y f`, again applied to F[0].
   I read `LowerShriek`: this functor is exactly derived open extension by zero
   followed by proper derived direct image. I obtained the helper's current source
   with `scompile.py --source Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude`:
   its real data supplies locally Noetherian and compact-space instances from Y's
   finite-type field structure and returns `NagataCompactification f`.
   No extra compactification or Noetherian hypothesis is imposed on the caller.
   I read `EtaleCompactSupportComparisons` and the bounded-below/unbounded
   compatibility declaration in `LowerShriek`; on F[0] this candidate has the
   required compactification-independent interpretation. Verdict: matches.
7. If every geometric fibre has dimension at most d, `R^q u_!F = 0` for q > 2d:
   `∀ (d : ℕ), (∀ y : Y, topologicalKrullDim (...) ≤ (d : WithBot ℕ∞)) →
   ∀ (q : ℤ), 2 * (d : ℤ) < q → IsZero (...)`.
   The displayed scheme is exactly the pullback of f along
   `Spec (AlgebraicClosure (Y.residueField y)) ⟶ Y`; it does not use the
   proper morphism in the compactification. The homology functor is in degree q
   on exactly the object in item 6. Quantifiers are separatedness, arbitrary d,
   its fibre bound, arbitrary q, then the strict inequality. Verdict: matches.

Dependency and delivery audit: I opened the recorded nodes and the declarations for
constructible complexes, ordinary direct image, scheme conventions, coefficient
conventions, ordinary derived categories, compact support, and topological Krull
dimension. I read the current general finite-type theorem using
`scompile.py --source Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`,
and opened `ProperBoundedConstructible` and the compact-support amplitude theorem.
Their coefficient categories, constructibility predicates and degree-zero objects
agree with this module. The already-landed amplitude node is the only added
`stmt_deps` entry, appropriately owning the helper used in the signature. No new
definition nodes or dependency modules are delivered, so H12/H13 add no further
delivery records to inspect. The module contains one public theorem, wholly `sorry`,
and no definitions, private copies, local notation or local instances. Its docstring
names the source/blueprint and reproduces all five proof steps, including the
Noetherian/finite-type checks, comparison, and additive-exponent argument.

Edge cases: empty X, empty Y and the zero sheaf are admitted; no nonemptiness or
nonzero hypothesis occurs. An empty geometric fibre has dimension bottom. For d = 0
the last clause gives vanishing for positive q; it asserts nothing at q = 2d.
All q are integers, and all d are natural dimension bounds as in the amplitude node.
N = 0 is deliberately excluded by the source's positive-annihilator convention;
the zero coefficient ring is permitted (N = 1), and both positive characteristic
and characteristic zero are covered by invertibility of N. The algebraic-closure
fibres use the actual residue fields, without quantification over an independently
smaller universe. Schemes/field in u and coefficient modules in u+1 follow the
recorded small-etale category; u is arbitrary and there is no extra universe equality.

Independent duplicate searches used vocabulary different from the first worker's:

- LeanFinder via msearch: `Etale sheaf cohomology proper support cohomological dimension
  twice fiber dimension constructibility finite coefficients`: eight hits on etale
  sites, morphism properties and affine limits, no matching theorem.
- Loogle via msearch: `"constructible", "homology"`: zero hits.
- LeanSearch via msearch: `Higher direct images with proper support of torsion
  constructible etale sheaves vanish above twice the geometric fiber dimension`:
  eight hits on etale morphisms, properness and ideal-sheaf support, no match.
- Mathlib grep via msearch: `constructible.*cohomology|pushforward.*constructible|
  compact.*support.*vanish` in AlgebraicGeometry: zero hits. Direct rg in Mathlib
  AlgebraicGeometry found no `isBoundedConstructible` or
  `IsConstructibleEtaleModuleSheaf` occurrence.
- Direct rg in upstream `WeilConjectures` and project `lean/Sheaf` found the
  related finiteness modules. I opened upstream
  `SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`, including
  `isZero_homology_rightDerivedLowerShriek_singleFunctor`: it states only the
  vanishing clause, using upstream `IsConstructibleSheaf` and a different
  all-geometric-test-field formulation. The accompanying bounded-constructibility
  theorems likewise use upstream `boundedConstructible`. None is an exact existing
  declaration of this three-clause node with its recorded notions. The project
  finite-type theorem and amplitude theorem are the cited ingredients, not another
  statement of all three clauses. The proposed full theorem name and blueprint-id
  name-map search found no collision.

Mismatch/change verdict: no mathematical, signature, dependency, docstring or convention
mismatch found; the Lean module and node record are retained unchanged. I checked that
`lean.statement` equals the file's complete signature verbatim, including newlines,
and checked every binder/universe by eye. This reading adds this independent audit
and its searches only. Compilation and the delivery dry run are recorded below.

Second-reader validation: `scompile.py Q34 sbc-thm-finiteness-finite-type
lean/Sheaf/AlgebraicGeometry/FiniteTypeSheafFiniteness.lean` compiled both the
sandbox signature probe and the library module cleanly, with no warnings or errors.
`deliver2.py Q34 sbc-thm-finiteness-finite-type --no-push` then printed
`OK (dry run): commit dd155cd838 passes the preflight and compiles; nothing pushed`.
Only this validation paragraph was appended after that successful dry run; no Lean
or node data changed.
