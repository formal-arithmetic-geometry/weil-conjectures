## Worker report

Module: `Sheaf.AlgebraicGeometry.FibrewiseVeryAmpleEvaluation`.
Declaration: `AlgebraicGeometry.fibrewise_very_ample_evaluation`.
One theorem, with its entire proof `sorry`; no new definitions or helper theorems.
The theorem docstring records all eight proof steps, their DAG prerequisites and sources.
No statement correction and no statement dispute.

Hypotheses and clauses, read against the DAG statement:

- Schemes and morphism: `{Y T : Scheme.{u}} (f : Y ⟶ T)`.
- Flat: `[Flat f]`. Proper: `[IsProper f]`. Finite presentation:
  `[LocallyOfFinitePresentation f]` together with properness, which supplies
  quasi-compactness and quasi-separatedness. This is finite presentation, with no
  hypothesis on the base scheme itself.
- Invertible line: `(L : Y.Modules) [L.IsInvertible]`, the recorded Zariski-locally
  rank-one module notion.
- Every geometric fibre has dimension at most one: `hdim` quantifies over
  `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and every `a : Spec (.of Ω) ⟶ T`;
  its inequality is `topologicalKrullDim (pullback f a) ≤ (1 : WithBot ℕ∞)`.
- Vanishing H1: `hH1` uses exactly the recorded O-module cohomology functor
  `RingedSpace.moduleCohomology (pullback f a).toRingedSpace 1`, applied to the
  tensor pullback of L along `pullback.fst f a`. `IsZero` is categorical vanishing
  in the module category, not cohomology of a different underlying sheaf.
- Complete linear system gives a closed immersion: `hvery` asserts epimorphy of
  the canonical evaluation counit on the geometric fibre and a closed immersion
  `j` which `Classifies` that very quotient. Its coefficient module is the actual
  direct image along `pullback.snd f a`, not a chosen subspace of sections.
  Since the base is Spec Ω, this is precisely the quasi-coherent sheaf associated
  to the full vector space H0 of the fibre. The existential quasi-coherence proof
  only makes P(H0) well-typed; proper quasi-coherent direct image guarantees it.
  The classifying condition explicitly carries the quotient-preserving O(1)
  identification. Thus this hypothesis describes the specified complete system,
  rather than merely an unrelated embedding witnessing relative very ampleness.
- E is f_*L: every occurrence uses `(pushforward f).obj L` literally, with no
  independent E or freely chosen identification.
- Finite locally free, allowing varying rank: the first conclusion is
  `((pushforward f).obj L).IsFiniteLocallyFree`, the existing variable-rank
  predicate from the dependency's LocallyFree module. There is no global rank.
- Arbitrary canonical base change: the second conclusion quantifies over every
  scheme `T' : Scheme.{u}` and `h : T' ⟶ T` and states `IsIso` of
  `moduleBaseChangeMap f (pullback.snd f h) h (pullback.fst f h)
  pullback.condition L`. This is the recorded normalized tensor-pullback mate,
  not existence of an arbitrary module isomorphism. The two projection maps
  and their actual cartesian-square equation are used.
- Surjectivity of evaluation: `Epi ((tensorPullbackSectionAdjunction f).counit.app L)`.
  Epimorphisms of sheaves of modules are exactly locally/stalkwise surjective maps.
- Closed evaluation embedding into the quotient projective bundle: the existential
  hE, D and j use the fixed `SymmetricAlgebraSheaf.gradedAlgebraData` applied to
  f_*L. `IsClosedImmersion j` supplies the geometric assertion; `Classifies D f L`
  of the same counit supplies the factorization over T and an isomorphism
  `j^*D.line ≅ L` carrying the universal quotient to evaluation.
- Quotient convention and actual O(1): `TautologicalQuotient` is the dependency's
  existing record, with its degree-one affine twisting charts and normalized
  generator equation. It fixes the quotient of the symmetric-algebra relative
  Proj. No dualization of E and no alternate projective-bundle construction occurs.
- Embedding and twist commute with arbitrary base change: for each T' and h the
  last conclusion supplies the base-changed evaluation quotient's D' and closed
  classifying map j'. Its coefficient module is literally f'_*p^*L. The comparison
  r satisfies `IsPullback r π' π h` and `pullback.fst f h ≫ j = j' ≫ r`.
  Finally `Classifies D (π' ≫ h) D'.line (...) r` specifies the comparison's
  twist isomorphism and quotient equation. The displayed quotient is the canonical
  composition comparison followed by π'^* of the exact base-change map, followed
  by D'.quotient. Hence r is the canonical bundle comparison under the already
  proved base-change coefficient identification. Together the two classifying
  equations also give compatibility of the embedding's twisting-line
  identification: both maps preserve the same epimorphic quotient.
- No reducedness, Noetherianness, quasi-compactness, connectedness or nonemptiness
  assumption is imposed on T, Y, T', or the geometric fibres.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.moduleCohomology`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank` and its variable-rank sibling
  `SheafOfModules.IsFiniteLocallyFree`. Both are actual local-generators predicates.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle`, read to fix the canonical symmetric-algebra
  relative-Proj convention used here. The theorem states the specific embedding,
  rather than just this projectivity predicate.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and
  `tensorPullbackSectionComp`, with the upstream `tensorPullback` and `pushforward`.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap`, defined by the normalized
  tensor adjunction and pushforward-composition maps.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData`:
  `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.TautologicalQuotient`,
  `Classifies` and the latter's `pulledQuotient`. Their definition-node owner is
  `def-per-projective-bundle-quotient-data`. The separate quotient-geometry theorem
  remains a proof dependency, imported from
  `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`.

Added to stmt_deps the four existing, already recorded nodes
`def-pc-module-pullback`, `def-sfb-module-base-change-map`,
`def-per-projective-bundle-quotient-data`, and
`def-sc-finite-locally-free-sheaf` to attach these existing canonical
interfaces; no dependency record changed. Their statement imports are public;
the quotient-geometry theorem itself remains a plain proof import through its
separate module. All ten proof dependencies' recorded modules are imported, with
proof-only imports plain. Their signatures and docstrings were read, including the
source Cech/perfect direct-image interface and the degree-zero mate square.

Sources opened locally: Stacks spaces-perfect.tex, flat-proper-perfect-direct-image-general
at line 6225 (0CTM); its scheme counterpart in perfect.tex at line 7525 (0B91);
more-algebra.tex line 19594 (0BCD); constructions.tex line 4672 and the subsequent
quotient classification (01OB/01OA); spaces-more-morphisms.tex line 11642 (05XA).
The source-based argument makes no base regularity assumption.

Edge cases checked before and after writing:

- Empty T: all geometric hypotheses and pointwise local-freeness conditions are
  vacuous; Y is empty and the canonical evaluation/bundle constructions apply.
- Empty fibres and rank-zero E: P(0) is empty; the empty evaluation embedding is
  allowed. No positive rank, nonempty coordinate type or nonempty fibre is assumed.
- Zero-dimensional fibres: the bound is an inequality, not pure dimension one.
- Nonreduced bases, including dual numbers: the proof uses the universal closed
  immersion locus with all test schemes and a stalkwise unit argument, not a
  reduced geometric-point detection assertion.
- Non-quasi-compact base and unbounded ranks across components: the variable-rank
  finite locally free predicate and local proof have no finite cover requirement.
- Identity and arbitrary nonflat/empty/open base changes: every h is quantified,
  and the same fixed canonical moduleBaseChangeMap is used throughout.
- Characteristic is arbitrary, including positive characteristic. The geometric
  point fields and schemes share universe u, so algebraic closures of every
  residue field are available; no independent smaller test universe is used.

Searches for an existing statement (actual wrapper results are also in searches.jsonl):

- msearch.py, `leanfinder`, query: "Fibrewise very ample invertible sheaf with
  vanishing H1 on a proper flat finitely presented scheme has locally free
  pushforward commuting with arbitrary base change and evaluation is a closed
  immersion". Eight hits: closed-immersion base-change permanence, properness,
  flatness; no cohomology/evaluation consequence.
- msearch.py, `loogle`, query:
  `AlgebraicGeometry.IsVeryAmple, Scheme.Modules.pushforward`.
  Zero hits; IsVeryAmple is not a Mathlib identifier.
- msearch.py, `grep`, query: `fibrewise|IsVeryAmple|evaluation`, subdirectory
  `AlgebraicGeometry`. Fourteen unrelated Mathlib hits; no matching theorem.
- msearch.py, `leansearch`, query: "For a proper flat finitely presented family
  and invertible sheaf fibrewise very ample with H1 zero, the pushforward is finite
  locally free, commutes with base change, and evaluation gives a closed immersion".
  Eight hits on pushforward and closed-immersion/proper permanence; no exact match.
- rg on project `lean/WeilConjectures` and `lean/Sheaf`:
  `fibrewise.*[Aa]mple|very[Aa]mple|VeryAmple|evaluation.*[Ee]mbed|Evaluation.*[Ee]mbed`.
  Found the proper-fibrewise-ample projectivity theorem and numerical very-ample
  criteria, but no theorem with this evaluation/base-change conclusion.
- rg on Mathlib and both project roots:
  `evaluationCounit|DirectImageEvaluationEmbedding|directImageEvaluation|fibrewise_very_ample_evaluation`.
  Only unrelated evaluation maps. A search for the item id upstream found none;
  Sheaf's ArithmeticStableOpenBounded mentions the node only in its proof plan.
- Read upstream `IsVeryAmple`: it witnesses an embedding by some finite subsystem;
  it does not itself name the full-section evaluation map, so hvery states that
  map directly with the existing quotient-classification interface.

Validation: prescribed scompile.py compiled the delivered module in both sandbox
and final library module modes, cleanly (5.5 s and 5.6 s respectively). No diagnostic
commands or generated helper proofs are left in the file.

## Second reading by Q14

Second pass by the assigned worker; no other agent was started, as the dispatcher
brief forbids that. The maintainer supplies the independent review of this delivery.
Re-read the node and final Lean side by side: all hypotheses and clauses are mapped
above. In particular, the dimension bound is retained despite not being needed by
the recorded proof; hvery uses all global sections, variable rank is explicit, and
both the module base-change map and the bundle comparison are canonically pinned.
The final classifying equation retains the twisting quotient as well as the
commutative square of scheme maps. No mismatch or statement change was found.

## Repair of returned head 63fa7f68bacd

H2, statement dependency ownership: replaced
`lem-weil-pbc-module-base-change-map-open-restriction` in stmt_deps with
`def-sfb-module-base-change-map`, whose existing Q51 record owns exactly
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap`. Re-read the definition's
full signature and adjunction-mate body in the recorded upstream module.

Replaced `lem-trf-projective-bundle-quotient-geometry` in stmt_deps with
`def-per-projective-bundle-quotient-data`, whose existing record owns precisely
`TautologicalQuotient`, `pulledQuotient` and `Classifies` in the already public-imported
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData`. Re-read all three declarations
and their docstrings. The theorem `lem-trf-projective-bundle-quotient-geometry` remains
in proof_deps, and its theorem module remains a plain proof import.

The retained returned-head node and current live node agree in every field other
than the delivery's stmt_deps and lean record. The two substitutions above are the
only repair changes to the node. The Lean module, signature, mathematical statement,
proof plan, proof_deps and all dependency records are unchanged. The delivery wrapper
rebases the retained work onto current main in its authorized temporary worktree.

Repair second pass: checked both definition-node records against their recorded
source declarations and the delivered signature; each replacement supplies exactly
the plain data used by the statement, with no theorem needed to define that data.
All previously reviewed hypothesis and conclusion mappings remain applicable.
