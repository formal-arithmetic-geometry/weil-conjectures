## Worker report

The module `Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension` states
`AlgebraicGeometry.Etale.subsingleton_cohomology_of_isAlgClosed_of_constructible`, with
one `sorry` and no new definition. The node and source statement are unchanged.

Hypothesis and conclusion correspondence:

- Algebraically closed ground field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- A scheme over that field: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`; no separatedness assumption is added.
- Dimension at most d: `(d : ℕ)` and
  `hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
- Finite coefficients as in sbc-def-coefficient-conventions: `(N : ℕ)`,
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, and
  `hcoeff : IsSmoothBaseChangeCoefficients N Λ X`. The predicate asserts positive N,
  finite Λ, `(N : Λ) = 0`, and that N is a unit in the global sections of X.
  The finite instance also makes the constructibility predicate available; it repeats
  exactly the finiteness already required by the convention.
- A constructible Λ-sheaf: `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
- Every degree q > 2d: `(q : ℕ) (hq : 2 * d < q)`; ordinary sheaf cohomology has
  nonnegative degrees, as in the dependency's definition.
- Vanishing H^q: `Subsingleton` of the underlying abelian group obtained by
  `(cohomology AddCommGrpCat.{u + 1} X q).obj`. Its input is the degree-zero complex
  `DerivedCategory.singleFunctor _ 0` of the underlying abelian sheaf of F, using
  `sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat Λ) AddCommGrpCat)`.
  Thus the cohomology is exactly the recorded ordinary derived-section cohomology,
  rather than a separately defined or compactly supported theory.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`,
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` (publicly imported by the
  coefficient convention), whose constructibility clause uses
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`; this same predicate is used here.
- `def-weil-pbc-scheme-conventions` fixes no declaration; the finite-type classes
  are from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and the scheme base convention
  is the standard `Scheme.Over`.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`, including its docstring
  and definition by chains of irreducible closed subsets.
- Stated proof dependencies imported without public: `WeilConjectures.AlgebraicGeometry.Sites.
  FiniteSupport` (`Scheme.subsingleton_H_of_isSepClosed`) and
  `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
  (`Scheme.HasTorsionEtaleCohomologicalDimensionLE`). The other proof notions are already
  provided by the statement imports. `thm-sc-finite-type-torsion-cd` has no Lean record
  in the supplied DAG, so has no recorded proof-dependency module to import.

Edge cases checked: empty X has dimension minus infinity and is not excluded; the proof
plan handles it using the empty covering. For d = 0 the bound is q > 0, not q ≥ 0.
The zero sheaf and zero coefficient ring are allowed. No nonempty, connected, reduced,
separated or positive-dimensional assumptions are imposed. The invertibility requirement
is precisely the coefficient convention even for the empty scheme. Universes use the
established Scheme.{u}, k : Type u, Λ : Type (u+1) and module values in Type (u+1)
encoding, with every universe and binder explicit. Finite d is appropriate to the stated
finite-type scheme over a field.

Searches for an existing statement (msearch.py, group NO, this item):

- LeanFinder: "Etale cohomology of constructible finite coefficient sheaves over an
  algebraically closed field vanishes above twice the dimension": eight unrelated hits
  (cotangent etale locus, affine-limit zero sections and singular homology); no match.
- Loogle: `"cohomology", "dimension"`: zero hits.
- LeanSearch: "Etale cohomology finite type algebraically closed field vanishes above
  twice dimension": service unavailable, Internal Server Error.
- Mathlib grep: `cohomologicalDimension|subsingleton_H_of_two_mul|fibrewise_cohomological`:
  zero hits.
- rg over WeilConjectures and lean/Sheaf for
  `cohomologicalDimension|subsingleton_H_of_two_mul|fin4-lem-fibrewise-cohomological-dimension|fibrewise_cohomological`:
  found the upstream `Scheme.subsingleton_H_of_two_mul_add_lt` and
  `Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`, plus mentions in DirectImage.
  Their complete signatures and docstrings were read: they concern arbitrary torsion
  abelian sheaves and `Sheaf.H`, not this constructible module sheaf statement with the
  recorded `Etale.cohomology` functor. They do not assert exactly this node's statement.
- Declaration-name search over Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for
  `subsingleton_cohomology_of_isAlgClosed_of_constructible`: no preexisting declaration.

Server validation: scompile.py compiled this delivered file cleanly (1.6 s) with nice 19,
two threads and the 60-second per-file limit. No local compiler or lake build was run.
No new nodes, dependency modules, statement correction or disputed statement is needed.

## Second reading by NO

Independently opened the item node, its blueprint source paragraph, every statement-dependency
node and the actual coefficient, constructibility, cohomology and dimension declarations.
The source of this item is the blueprint, not a Stacks lemma. Also read Stacks
`topology.tex`, definition-Krull (0055), and `etale-cohomology.tex`,
lemma-equivalence-abelian-sheaves-point and lemma-compare-cohomology-point (03QU), including
the preceding assumptions: an arbitrary field K, a geometric point and its absolute Galois
group. These impose no extra hypothesis on this algebraically closed-field statement.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Algebraically closed field k': `(k : Type u) [Field k] [IsAlgClosed k]`.
   Exact: this is a field, not an arbitrary commutative ring or a separably closed-field
   replacement that would strengthen the statement.
2. Scheme X over k': `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
   Exact: the structure morphism is the standard `X ↘ Spec (.of k)` convention.
3. Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
   `[QuasiCompact (X ↘ Spec (.of k))]`. Exact: read Mathlib's class signatures and the
   scheme-conventions node; together these mean finite type. No separatedness, smoothness,
   properness, reducedness or extra Noetherian assumption is present.
4. Dimension at most d: `(d : ℕ)` and
   `hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. Exact: opened Mathlib's definition
   `krullDim (IrreducibleCloseds X)` and Stacks 0055. This is the dimension of X, not a
   relative dimension or the dimension of a chosen stratum. Natural finite d represents
   the finite nonnegative bound used in this statement and its proof; the empty scheme
   retains dimension minus infinity.
5. Finite coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` and
   `hcoeff : IsSmoothBaseChangeCoefficients N Λ X`. Exact: the opened definition is
   `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(X, ⊤))`, as the coefficient node and
   its source require. The explicit finite instance repeats an already required property
   to make the recorded constructibility predicate available; it adds no restriction.
   A global inverse of the constant section N is equivalent to its local invertibility.
6. Constructible Λ-sheaf F: `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
   `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. Exact: the constructible-complexes
   dependency imports this recorded sheaf predicate. Its definition uses a finite locally
   closed stratification with constructible parts, stratum inverse images via `upperStar`,
   and etale trivializations with finite constant module values. It does not use the
   different upstream finitely generated-stalk predicate.
7. All q > 2d: `(q : ℕ) (hq : 2 * d < q)`. Exact: ordinary sheaf cohomology degrees
   are nonnegative in the cohomology node; the implicit coercion to the functor's integer
   index preserves q. No boundary degree q = 2d is claimed. Objects and hypotheses precede
   the universally quantified degree, as in the node.
8. H^q(X_et,F) = 0: the conclusion is `Subsingleton` of the group underlying
   `(cohomology AddCommGrpCat.{u + 1} X q).obj` applied to the degree-zero complex of the
   underlying abelian sheaf of F. Exact: opened `Etale.rightDerivedGlobalSections` and
   `Etale.cohomology`; they are RΓ and its homology, respectively. `sheafCompose` with
   `forget₂ (ModuleCat Λ) AddCommGrpCat` is precisely forgetting the module action, and
   `DerivedCategory.singleFunctor _ 0` places that same sheaf in degree zero. A subsingleton
   abelian group is the zero group. No compact supports or finiteness conclusion is used.

Edge cases: empty X is permitted (dimension bottom satisfies hdim, and the empty covering
forces all abelian sheaves and their cohomology to vanish). An empty stratification is
permitted by the recorded constructibility predicate. Zero F and the zero coefficient
ring are permitted; no nontriviality hypothesis is added. At d = 0 only q > 0 is asserted;
q = 0 is never inadvertently claimed to vanish. In positive characteristic the only
coefficient restriction is the source's invertibility of N; characteristic zero is also
covered. Universe u is explicit and arbitrary, the field and scheme use the established
same-universe convention, and the finite ring and module values lie in Type (u+1), exactly
as the recorded dependencies require. There is no independently smaller test universe.

Independent searches, with different wording from the first reader:

- LeanFinder via msearch: "Cohomology of a torsion sheaf on a scheme over a separably
  closed field is zero above twice its dimension". Eight hits, including `Sheaf.H`,
  `Sheaf.cohomologyPresheaf`, group-cohomology vanishing and Tor/cotangent results;
  no matching scheme-dimension statement.
- Loogle via msearch: `"cohomology", "IsAlgClosed"`. Zero hits.
- LeanSearch via msearch: "Vanishing of higher derived global sections of finite module
  sheaves on finite type schemes over algebraically closed fields". Service returned
  Internal Server Error; recorded as unavailable, not a no-match verdict.
- Independent rg across Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `two_mul_lt_of_isSepClosed|two_mul_add_lt|cohomology.*[Dd]im|[Dd]im.*cohomology|fibrewise.*[Cc]ohom`.
  Opened both complete upstream `Scheme.subsingleton_H_of_two_mul_add_lt` and
  `Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed` signatures and docstrings. They
  quantify over arbitrary torsion abelian sheaves and conclude vanishing of `Sheaf.H`,
  the Ext-based theory. They do not state this node's constructible module-sheaf statement
  using the recorded derived-section functor. Its comparison with Sheaf.H is a stage-3
  bridge, not definitional equality, so these are not exact existing matches.
- Checked the proposed full declaration name against the upstream-name table and the
  source/project search results: no preexisting declaration.

No mismatch was found. No Lean, node statement or dependency change was needed, and no
new definition node or dependency module is present. No statement_change is present, so
citer revalidation for a correction is inapplicable. Read the proof dependencies for the
field and torsion-dimension steps; the docstring includes all three node proof steps,
including the empty-scheme case and the actual-dimension specialization. Stated proof
dependencies are supplied by the imports; the finite-type torsion bound currently has no
recorded Lean module. The file has one named theorem with sorry, no definition, no proved
lemma, no local notation or private instance, and no line exceeding 100 characters.
The node's lean.statement is verbatim the complete theorem signature in the file; all
binders and universes are bound.

Server validation: scompile.py compiled the delivered FibrewiseCohomologicalDimension
module cleanly in 1.7 s, also checking its coefficient and torsion-dimension side imports,
with nice 19, two threads and 60 seconds per file. No local compiler or global build used.
Second reading changes only this review report.
