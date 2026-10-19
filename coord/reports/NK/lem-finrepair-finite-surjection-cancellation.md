## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation` states
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_finite_surjective`.
Its only theorem proof is `sorry`. No new definition, dependency module, statement
correction, or disputed statement is needed.

Hypothesis and conclusion correspondence:

- The field `k` is `(k : Type u) [Field k]`.
- The finite coefficient ring fixed through `def-finrepair-property-c` is
  `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, with
  `hX`, `hS`, `hY : IsSmoothBaseChangeCoefficients N Λ ...` on the three schemes.
  The recorded predicate unpacks as positivity of N, finiteness, `(N : Λ) = 0`,
  and invertibility of N in global sections. These are precisely the inherited
  `sbc-def-coefficient-conventions`, not additional coefficient restrictions.
- The schemes are `{X S Y : Scheme.{u}}`. Each `Over (Spec (.of k))` supplies
  its structure morphism. `LocallyOfFiniteType` and `QuasiCompact` on that morphism
  together express finite type, as specified by the conventions dependency.
  The finite-type context on Y is required by the recorded C predicate and is
  inherited from the finite morphism π and X (as the node's second proof step
  explains). For any Y of the node one takes its composite structure map to k;
  the displayed Y hypotheses can then always be supplied. No separatedness,
  smoothness, properness, or algebraic closedness of k is required.
- The morphisms are `(f : X ⟶ S) (π : Y ⟶ X)`; `[IsFinite π]` is finite,
  and `[Surjective π]` is surjectivity on the underlying topological spaces.
- The antecedent is
  `h : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f)`.
  Composition order is Y → X → S, exactly the node's `fπ`.
- The conclusion is `HasConstructibleHigherDirectImages k N Λ hX hS f`.
  The imported definition quantifies over every natural q and every constructible
  sheaf in `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and asserts
  constructibility of `higherDirectImage Λ f (q : ℤ) F`. It includes degree zero
  and imposes no uniform vanishing condition.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention node, with no
  module or declaration of its own. Its recorded meanings used here are Mathlib's
  `AlgebraicGeometry.Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsFinite`,
  and `Surjective`. The full class signatures and docstrings were read in
  `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`, `QuasiCompact.lean`,
  `Finite.lean`, and `UnderlyingMap.lean`.
- `def-finrepair-property-c` records
  `AlgebraicGeometry.Etale.HasConstructibleHigherDirectImages` in
  `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`. Its full definition
  and docstring were read, and that exact declaration is used in both places.
  In particular the similarly named general-base predicate in
  `ConstructibleHigherDirectImage.lean` is not substituted for it.
- The full shared `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`
  declaration and docstring were read in
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`; it comes from the
  public import of the recorded C module.

All stated proof-dependency modules have ordinary, non-public imports. The
convention node has no module; `lem-fin-finite-morphism` has no Lean record yet.
The proof docstring follows all six node steps, including the germ-compatible
stalk-unit argument, constructible resolution, Leray row collapse only for the
constructible pullbacks, Cartan–Eilenberg first page, use of C(fπ), and eventual
stability and finite filtration in each degree. It does not use the blueprint's
stronger informal assertion of exact pushforward for arbitrary sheaves.

Edge cases checked: empty X forces empty Y by surjectivity, and no nonemptiness
hypothesis is imposed; if S is empty all source schemes are empty. Degree zero
is included. Zero coefficient rings are allowed. N=0 is excluded exactly by the
shared positive-N convention; N=1 permits zero coefficients. No restriction on
characteristic beyond the inherited invertibility convention is introduced.
The resolution can be unbounded to the right, so no degree bound appears.
The universe u is arbitrary, with the recorded module-sheaf universe u+1.

Searches for an existing declaration (2026-10-15):

- `msearch.py leanfinder`: "Constructibility of all higher direct images descends
  along a finite surjective morphism of schemes" returned eight results about
  constructible subsets, general flat descent, and locally surjective sheaves;
  none states this higher-direct-image cancellation.
- `msearch.py loogle`: `"constructible", "Sheaf"` returned zero hits.
- `msearch.py grep`: `constructib.*(surject|finite)|(surject|finite).*constructib`
  in Mathlib/AlgebraicGeometry returned two constructible-image results in
  Morphisms/FinitePresentation.lean, neither about module-sheaf direct images.
- `msearch.py leansearch`: "Constructibility of higher direct images descends
  along finite surjections" was unavailable (Internal Server Error).
- `rg` with the finite/surjective constructibility pattern in upstream
  `WeilConjectures` and project `lean/Sheaf` found component constructions and
  constructible finite pushforward material, but no cancellation statement.
  `grep -rn` for the exact node id in upstream returned no match. Searching
  `dag/lean_names_upstream.json`, both source trees, and Mathlib for the selected
  declaration name and finite-surjection higher-direct-image combinations
  returned no duplicate.

Validation: server-only `scompile.py NK lem-finrepair-finite-surjection-cancellation`
compiled the delivered module cleanly in 2.7 seconds, nice 19, two threads,
60-second per-file limit. The C and coefficient side dependencies also compiled
in the server's private overlay. No local compiler or library build was run.


## Second reading by NK

I independently read the sandbox node, its blueprint source (order 1598), all
six node proof steps, both statement-dependency nodes and their recorded
interfaces, and the coefficient-convention node and its definition. I also
opened the actual Mathlib classes for finite, surjective, locally finite-type
and quasi-compact morphisms, the constructible module-sheaf definition, and the
upstream higher-direct-image and lower-star definitions. The following is my
object/hypothesis/conclusion checklist, assembled from the natural statement.

1. Base field k: `(k : Type u) [Field k]`. This is the finite-type-over-k
   setting of the source and the recorded C predicate. Verdict: matches.
2. Fixed coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`
   and `hX`, `hS`, `hY : IsSmoothBaseChangeCoefficients N Λ ...`.
   The shared definition is exactly positive N, finite Λ, `(N : Λ) = 0`,
   and `IsUnit (N : Γ(T, ⊤))`. These are the conventions inherited through
   `def-finrepair-property-c`, with the same N and Λ everywhere. Verdict: matches.
3. Schemes X and S of finite type over k: `{X S Y : Scheme.{u}}`, the X/S
   `Over (Spec (.of k))` instances, and `LocallyOfFiniteType` plus
   `QuasiCompact` on their structure maps. The convention node explicitly
   defines finite type by this conjunction. Verdict: matches, no separatedness,
   smoothness, properness, nonemptiness or algebraic-closure assumption.
4. Scheme Y and morphism π: `(π : Y ⟶ X) [IsFinite π] [Surjective π]`.
   Mathlib IsFinite is affine with finite ring maps over affine opens;
   Surjective is surjectivity on underlying points. Verdict: exact meanings.
   Y's displayed finite-type context is needed to apply the recorded C
   definition and follows by choosing the composite Y → X → Spec k. N is
   then invertible on Y by pullback from X. Hence these explicit arguments
   exclude no Y of the natural statement. No `IsOver` requirement on π is
   added: the predicates concern the underlying schemes and sheaf maps and
   their bodies do not depend on the chosen field structure maps.
5. Morphism f: `(f : X ⟶ S)`, an arbitrary scheme morphism as written in the
   node. Verdict: no additional property or compatibility required.
6. Hypothesis C(fπ):
   `h : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f)`.
   Lean composition goes from Y through X to S. Verdict: exact antecedent,
   with the coefficient and finite-type contexts required by its definition.
7. Conclusion C(f):
   `HasConstructibleHigherDirectImages k N Λ hX hS f`.
   Opening that exact definition gives `∀ (q : ℕ) (F : Sheaf
   X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
   Scheme.IsConstructibleEtaleModuleSheaf F →
   Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)`.
   The upstream higherDirectImage is homology of derived direct image of F
   in degree zero. The shared constructibility definition is a finite
   constructible locally closed stratification with finite locally constant
   module values. Verdict: all degrees and every constructible module sheaf,
   exactly the conclusion, with no vanishing bound.

Source hypotheses: I read Stacks etale-cohomology.tex at
`proposition-finite-higher-direct-image-zero` (03QP),
`lemma-pullback-constructible` (095G), `lemma-constructible-abelian` (03RZ),
and `lemma-finite-pushforward-constructible` (095R). The last requires finite
presentation as well as finiteness, and the module statements require a
Noetherian coefficient ring. Here Λ is finite, hence Noetherian; X is finite
type over a field, hence locally Noetherian, so a finite π is finitely
presented. These are consequences, not missing hypotheses to add. The module
proof docstring correctly retains the six-step node argument, including the
stalk-unit compatibility, constructible resolution, Leray row collapse,
Cartan–Eilenberg spectral sequence, C(fπ), and stable pages with finite
filtration in each degree. It does not assume arbitrary-sheaf exactness from
the weaker recorded finite-morphism node.

Edge cases: empty X forces Y empty already because π exists; surjectivity
also rules out empty Y over nonempty X. Empty S forces X and Y empty. The
zero coefficient ring and zero sheaf are allowed. Degree zero is included
by `q : ℕ`; there is no bounded-degree hypothesis. N = 0 is excluded by the
inherited positive-N convention, while N = 1 permits the zero ring. There is
no new restriction on characteristic, only invertibility of N. The arbitrary
universe u and the recorded u+1 coefficient/sheaf universe are preserved;
there are no test-object universe quantifiers or unbound universes/variables.

Independent searches (2026-10-15), using words different from the worker's:

- `msearch.py leanfinder` with "Descent of constructible etale cohomology under
  a finite covering map": eight hits, about small/big etale topologies,
  affine-transition-limit auxiliaries, coherent-topology local surjectivity,
  and subcanonicity. None states this cancellation theorem.
- `msearch.py loogle` with `"higherDirectImage"`: zero hits.
- `rg -i` across Mathlib, upstream WeilConjectures and project lean/Sheaf
  with `constructible.*(cancel|descen|surject)|
  (cancel|descen|surject).*constructible|hasConstructibleHigherDirectImages_of`:
  subset topology, Noetherian/limit descent, immersion refinement, universal
  homeomorphism invariance, finite pushforward assertions and stalk-surjectivity
  loci; no finite-surjection cancellation of all higher direct images.
- Exact node-id and chosen-name search in upstream WeilConjectures and
  dag/lean_names_upstream.json: no matches. The only project C definition is
  the recorded `ConstructibleHigherDirectImages` definition; it is reused.

No mismatch in the statement or module was found, and neither was rewritten.
There are no new nodes, dependency modules, private definitions, hollow data,
local notations or local instances to review. The only proof is the named
public theorem's `sorry`; both docstrings contain the source and blueprint id.
The node lean.statement was checked verbatim against the signature, and all
lines meet the 100-character limit. The only change is this reading report.
No statement correction or citer-verdict review is necessary.

Validation: my server-only scompile.py run compiled the delivered module
cleanly in 2.8 seconds (nice 19, two threads, 60 seconds per file). Its side
coefficient and C imports compiled in 1.4 and 2.5 seconds in the private overlay.
No local compiler or global build was run.
