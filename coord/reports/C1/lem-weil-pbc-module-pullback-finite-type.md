## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ModulePullbackFiniteType.lean` states
`AlgebraicGeometry.Scheme.Modules.tensorPullback_isFiniteType`.  It takes schemes
`X Y`, a morphism `f : X ⟶ Y`, and a module `G : Y.Modules` with the hypothesis
`[G.IsFiniteType]`; its conclusion is
`((tensorPullback f).obj G).IsFiniteType`.  `SheafOfModules.IsFiniteType` is
Mathlib's local finite-generation predicate: its `exists_localGeneratorsData`
clause renders the node's assertion that every point has an open neighbourhood
with a finite direct-sum structure-sheaf epimorphism.  The pullback module uses
the same finite number of generators after inverse image of the neighbourhood,
as stated by the node's parenthetical clause.

The declaration is a theorem with proof `sorry`, as required at stage 2.  The
module imports `Sheaf.AlgebraicGeometry.TensorPullback`, whose declaration
`AlgebraicGeometry.Scheme.Modules.tensorPullback` is the recorded Lean
declaration for dependency `def-pc-module-pullback`.

Dependencies used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and its morphisms
  (`X ⟶ Y`) provide the scheme objects and morphism in the theorem.
- `pqf-def-coherent`: `SheafOfModules.IsFiniteType` provides the finite-type
  hypothesis and conclusion (the recorded project declaration is
  `AlgebraicGeometry.RingedSpace.IsCoherent`; its finite-type clause is the
  Mathlib predicate used here).
- `def-pc-module-pullback`: project declaration
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` in
  `Sheaf.AlgebraicGeometry.TensorPullback` provides the pullback functor.

Statement clauses rendered in Lean:

- “Let `f : X → Y` be a morphism of schemes” is `(X Y : Scheme.{u})`
  and `(f : X ⟶ Y)`.
- “Let `G` be an `O_Y`-module of finite type” is `(G : Y.Modules)` with
  instance hypothesis `[G.IsFiniteType]`.
- “The pullback is of finite type” is the conclusion
  `((tensorPullback f).obj G).IsFiniteType`; this predicate expands to local
  finite direct-sum generators, including the `n = 0` case.

Edge cases checked: the Mathlib predicate permits `n = 0` (zero module), does
not require nonempty schemes, and has no characteristic or separation
hypotheses.  The statement therefore retains the empty-index and zero-module
cases from the node.  The universe is explicitly bound by `universe u`.

Searches made:

- `msearch.py ... leanfinder "pullback of a finite type sheaf of modules along a morphism of schemes is finite type"`: found Mathlib scheme pullback and finite-morphism results, but no preservation theorem.
- `msearch.py ... loogle "SheafOfModules.IsFiniteType, tensorPullback"`: zero hits; `tensorPullback` is unknown to Loogle.
- `msearch.py ... grep "IsFiniteType|tensorPullback" AlgebraicGeometry/Modules`: zero hits.
- Existing node and source searches (`rg`/`grep`) found the project tensor pullback module and no theorem with this statement.  The node's recorded LeanSearch, LeanFinder, Loogle, grep, and local-search entries were also reviewed; they report no exact pullback-preserves-finite-type declaration.

Compilation with `scompile.py` succeeded without errors or warnings (the
expected declaration-uses-`sorry` warning is absent from the clean result).

## Earlier second reading (a previous round; superseded)

I reread the item statement and the module signature together.  The variables
`X`, `Y`, and `f : X ⟶ Y` render exactly the scheme-morphism hypothesis; `G` and
`[G.IsFiniteType]` render the finite-type module hypothesis; and the result is
the finite-type predicate on the object of the recorded `tensorPullback` functor.
No hypothesis, object, or edge case is added or omitted.  The dependency
declarations named above were opened and their signatures checked.  The only
change after the first dry run was mechanical: the node record now includes its
module `file`, uses branch `sheaf-dag`, and records the parser's signature
without the terminating `:=`.


## Second reading by C1

I independently opened the node, its four proof steps, the module, all three
statement-dependency nodes, and their actual declarations. The source is
[Stacks 01B6](https://stacks.math.columbia.edu/tag/01B6), with the open-restriction
argument of [01B3](https://stacks.math.columbia.edu/tag/01B3) and the finite-type
definition [01B5](https://stacks.math.columbia.edu/tag/01B5).
The repository has no literature/stacks-project/modules.tex on this machine;
I also read the actual TeX labels and proofs at lines 730–850 of
/home/ubuntu/weil-sandbox/H1/lem-weil-pbc-module-stalk-exact/scratchpad/modules.tex.
The source assumes only ringed spaces and a ringed-space morphism, so its scheme
specialization has no Noetherian, quasi-coherent, separation, field, or
characteristic hypothesis.

The object/hypothesis/conclusion list, matched against the final Lean:

- Schemes X and Y: `(X Y : Scheme.{u})`, with Scheme and Scheme.Hom opened in
  Mathlib.AlgebraicGeometry.Scheme (structure Scheme and structure Hom).
  Verdict: exactly the schemes and scheme morphisms of def-pc-scheme.
- Morphism f : X → Y: `(f : X ⟶ Y)`. Verdict: no extra geometric property.
- An O_Y-module G: `(G : Y.Modules)`. Mathlib's `Scheme.Modules` is
  `SheafOfModules.{u} Y.ringCatSheaf`, on the Zariski opens. Verdict: the correct
  module category, not etale sheaves or modules over global sections.
- G of finite type, namely a finite free surjection locally at every point:
  `[G.IsFiniteType]`. Opened Generators.lean: LocalGeneratorsData covers the
  terminal object by opens, GeneratingSections supplies an epimorphism from
  the free module, and its IsFiniteType requires a finite generator index.
  Verdict: precisely the finite-type clause of pqf-def-coherent; its landed
  Coherent.lean explicitly uses this Mathlib predicate. No coherence or
  quasi-coherence instance is assumed. CoversTop on opens means their union is
  the entire space, giving the pointwise neighbourhood formulation.
- The pullback f^*G: `(tensorPullback f).obj G`. Opened TensorPullback.lean:
  tensorPullbackObj changes rings on the abelian inverse image along the
  adjoint structure-sheaf map; tensorPullback is the resulting functor.
  Verdict: the recorded def-pc-module-pullback tensor formula, not Mathlib's
  separately defined abstract left adjoint. Its data have no sorry; the
  functor laws and comparisons use separately named postponed theorems.
- Pullback of finite type: first conjunct
  `((tensorPullback f).obj G).IsFiniteType`. Verdict: all points are covered
  by finite free generating surjections, as required.
- The parenthetical clause chooses U = f⁻¹V with the same n: second conjunct
  quantifies over `(V : Y.Opens) (n : ℕ)` and a finite-free map φ to `G.over V`;
  from `Epi φ` it asserts a map ψ with `Epi ψ` to the restriction of f^*G on
  `((TopologicalSpace.Opens.map f.base).obj V)`, from the free sheaf on the
  same `ULift.{u} (Fin n)`. Opened Free.lean (`free` is a coproduct of unit
  sheaves) and PushforwardContinuous.lean (`over` is restriction to the
  over-site). Verdict: the exact inverse-image open and the same number of
  summands. For V containing f(x), this open contains x. Quantifying over a
  chosen surjection makes explicit the node's choice of local presentation;
  it adds no new hypothesis to the outer statement. Epi is sheaf surjectivity
  here, as used in the node's steps 2 and 4.

Edge cases: n = 0 is included by ℕ and Fin 0 is empty; ULift changes only the
universe, not the number of generators. The zero module and empty schemes are
allowed; there is no Nonempty hypothesis. V may be empty and its inverse image
is empty. Arbitrary commutative structure rings, including characteristic zero
and every positive characteristic, are allowed. `universe u` explicitly binds
the scheme and module size; all finite generator types are lifted to that
universe, and no unrelated smaller test universe occurs. No free variables or
universe parameters remain. The single-scheme-category universe convention is
inherited from the recorded tensorPullback and Mathlib Scheme.Hom.

Independent searches (different wording from the first worker):

- msearch LeanFinder: "finite generation of sheaves preserved by inverse image
  extension of scalars": eight results, including IsFiniteType and finite
  presentation predicates, but no preservation statement.
- msearch Loogle: "SheafOfModules.IsFiniteType": four results (the predicate,
  constructor, local-generators field, and finite-presentation implication),
  none asserting pullback preservation.
- msearch LeanSearch: "inverse image extension of scalars preserves locally
  finitely generated sheaves": service unavailable (Internal Server Error);
  recorded as unavailable, not as evidence of absence.
- msearch grep: "IsFiniteType|finiteType" in Algebra/Category/ModuleCat/Sheaf:
  generator and presentation predicates and instances only. Directly read
  Generators.lean:178; it transports globally generating sections under a
  colimit-preserving functor, not local generators under a scheme morphism.
- rg "IsFiniteType|isFiniteType" over WeilConjectures and lean/Sheaf found
  finite-descent, locally-free, coherent-kernel and finite-presentation
  results, affine quasi-coherent global-generators results, and a tensor
  globally-generated theorem; no exact pullback statement. The etale
  finite-type predicate concerns another site and coefficient category.
- rg for tensorPullback_isFiniteType in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no declaration with that name. No new
  notion is introduced and no dependency replacement module is needed.

Mismatches repaired:

1. H3: the former conclusion only asserted IsFiniteType, and did not formally
   assert the node's inverse-image-open/same-n clause. Added the explicit
   second conjunct, using only existing Mathlib restriction and free modules.
   The natural-language node and its dependencies remain unchanged.
2. H8: the former docstring described the conclusion but omitted the node's
   complete proof. Added its four steps with the cited dependency IDs:
   restriction and composition, preservation of the epimorphism, identifying
   the finite free pullback, and the composite surjection giving finite type.
3. H9: added the standard copyright/license/author header. During compilation
   corrected Opens.map application to its functor object `.obj V`.
4. Updated lean.statement from tools/stage2_delivery.py's exact signature
   extraction, including the new conjunct.

All proofs remain `sorry`; there are no definitions or instances introduced
by this delivery. Both imports are used, every Lean line is at most 100
characters, and the source and blueprint marker are in both docstrings.
The Worker report and the superseded earlier reading are retained as history;
this section records the final conclusion, including the repaired clause.

Validation: scompile.py C1 lem-weil-pbc-module-pullback-finite-type on
ModulePullbackFiniteType.lean returned exit 0, compiled in 3.0 seconds,
with no errors or warnings.
