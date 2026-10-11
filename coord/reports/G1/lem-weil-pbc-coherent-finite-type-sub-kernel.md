## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CoherentFiniteTypeSubKernel.lean` states
`AlgebraicGeometry.RingedSpace.coherent_finiteType_submodule_kernel`. It fixes a
ringed space `X` (a scheme is represented by its underlying ringed space) and gives
the two clauses of Stacks 01BY as a conjunction of independently quantified
implications.

For clause (1), `K` and `G` are sheaves of modules over `moduleRings X`, `i : K ⟶ G`
is the subsheaf inclusion and `[Mono i]` renders injectivity, `K.IsFiniteType` is
the finite-type hypothesis, and `IsCoherent X G → IsCoherent X K` is the
conclusion. For clause (2), `φ : F ⟶ G` renders the module morphism,
`F.IsFiniteType` and `IsCoherent X G` render the hypotheses, and
`(kernel φ).IsFiniteType` renders that the sectionwise kernel is of finite type.
The universal quantifiers keep the two parts independent, so no hypothesis from
one part is imposed on the other.

The module imports `Sheaf.AlgebraicGeometry.Coherent`, whose declaration
`AlgebraicGeometry.RingedSpace.IsCoherent` defines finite type plus finite-type
kernels of maps from finite free modules, using Mathlib's
`SheafOfModules.IsFiniteType`. The ambient scheme notion is Mathlib's
`AlgebraicGeometry.Scheme`; the sheaf/module category is Mathlib's
`SheafOfModules` (dependency `def-weil-sheaf-of-modules-category`).

Edge cases checked: `n = 0` is included by the dependency's `Fin n`; the zero
sheaf and zero morphism are allowed; the universal sheaf quantifiers include
empty schemes and arbitrary opens. The index universe is fixed to the sheaf
universe `u`.

Searches recorded in the node were checked: LeanSearch, LeanFinder, Loogle,
grep over Mathlib, and project `rg` searches found only
`SheafOfModules.IsFiniteType` and no theorem for coherent subsheaves or kernels.
The project declaration `AlgebraicGeometry.RingedSpace.IsCoherent` was used for
the coherent notion; no duplicate definition was added.

## Earlier second reading (a previous round; superseded)

The first conjunct exactly states the finite-type subsheaf implication with a
monomorphism as the subsheaf inclusion. The second conjunct independently
quantifies a morphism and states finite type of its categorical kernel. The
coherent predicate and finite-type predicate are imported declarations, so the
statement introduces no private carrier or altered notion. No statement fault
or correction was found.

## Second reading by G1

Independent review with the node, delivered module and dependency declarations open.
I read `modules.tex` lines 1550–1695 in the server's literature checkout, including
Definition 01BV, Lemma 01BY and its first two proof paragraphs. The local machine
does not contain that checkout. The source assumes only a ringed space; it imposes
no Noetherian, quasi-coherent, separation, characteristic or field hypothesis.
The official Stacks pages https://stacks.math.columbia.edu/tag/01BY and
https://stacks.math.columbia.edu/tag/01BV also confirm these assumptions.

Object/hypothesis/conclusion checklist, all passing:

1. Ambient `X`: `(X : RingedSpace.{u})` renders the node's explicit extension
   to arbitrary ringed spaces. On schemes instantiate with `X.toRingedSpace`.
   I opened `def-pc-scheme` and Mathlib's `Scheme` structure: it extends
   `LocallyRingedSpace`, hence has the required underlying ringed space.
2. Structure sheaf and modules: `moduleRings X` is the existing abbreviation
   in `Sheaf.Paper.DerivedHomMayerVietoris`, formed from `X.sheaf` by forgetting
   commutativity. `SheafOfModules.{u} (moduleRings X)` is the recorded Mathlib
   notion of `def-weil-sheaf-of-modules-category`. I opened its structure and
   `Hom`: an underlying presheaf of modules with a sheaf condition, and
   sectionwise linear morphisms. No replacement carrier is introduced.
3. Coherence/finite type: I opened `pqf-def-coherent` and
   `Sheaf.AlgebraicGeometry.Coherent`. `RingedSpace.IsCoherent X F` is exactly
   finite type plus finite-type kernels of every map from a finite free module
   on every open. The free module uses `ULift (Fin n)`, restriction uses `over`.
   Mathlib `IsFiniteType` in `Sheaf/Generators.lean:142` means locally finitely
   generated sections, matching 01B5; it is not global finite generation.
4. Part (1) objects: independently universally quantified `K G` and `i : K ⟶ G`.
   `[Mono i]` renders a subsheaf inclusion up to isomorphism onto its image.
   Evaluation preserves finite limits (`Sheaf/Limits.lean`), so it sends a
   mono to a mono of modules, i.e. an injective section map. Conversely the
   faithful underlying-presheaf functor and sectionwise injectivity make a mono.
   The image is thus an actual submodule on every open, exactly as in the node.
5. Part (1) hypotheses: `K.IsFiniteType` and `IsCoherent X G`, with no extra
   assumption on either object. Conclusion: `IsCoherent X K`, exactly coherence.
6. Part (2) objects: independent universal `F G` and `φ : F ⟶ G`; `φ` has no
   mono, epi, injective or surjective requirement.
7. Part (2) hypotheses: `F.IsFiniteType` and `IsCoherent X G`, exactly the node.
   Conclusion: `(kernel φ).IsFiniteType`. The categorical kernel is the
   sectionwise kernel up to its canonical isomorphism: Mathlib's evaluation
   functors preserve finite limits. Finite type is invariant under isomorphism.
8. Conjunction: the two independent universal implications give both clauses;
   neither part inherits assumptions from the other. The order of `K G` and
   of the two implication hypotheses does not change their quantifier scope.

Edge cases: no nonempty assumption excludes the empty scheme or empty open;
the finite-type local cover can be empty on an empty space. Zero sheaves,
zero morphisms and noninjective maps in part (2) are allowed. `n : ℕ` in the
coherent dependency includes `n = 0`, where `ULift (Fin 0)` is empty. No field,
domain or characteristic is assumed. `universe u` is bound explicitly, and
all objects use the established `RingedSpace.{u}` / module-universe encoding;
`u` can be raised to include larger data. There is no separate universe
of test objects that could make a hypothesis vacuous.

Independent searches, with different terms from the first worker:

- `msearch.py leansearch "locally finitely generated subsheaf of a coherent
  module sheaf is coherent"`: unavailable (Internal Server Error), logged;
  this is not evidence of absence.
- `msearch.py leanfinder "relations kernel of a morphism of locally finitely
  generated sheaves into a coherent sheaf on a ringed space"`: eight hits,
  including `Presentation.relations`, `relationsOfIsCokernelFree`,
  `IsFinitePresentation`, and scheme ideal-sheaf kernels; none states either
  clause about Stacks-coherent module sheaves.
- `msearch.py loogle "SheafOfModules.IsFiniteType"`: four declarations about
  the finite-type predicate and finite presentation, none the target theorem.
- `msearch.py grep "finiteType.*ker|finite_type.*ker|coherent|finiteType.*sub"`
  in `Algebra/Category/ModuleCat/Sheaf`: only quasi-coherent data hits.
- Direct `rg "isCoherent|IsCoherent|coherent.*kernel|coherent.*sub"` on
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`:
  no exact existing statement. I opened the upstream `Modules/Coherent.lean`:
  `Scheme.Modules.isCoherent` is quasi-coherent plus finite presentation,
  explicitly weaker than 01BV on general schemes, hence unusable here.
  Upstream quasi-coherent-kernel theorems likewise concern another property.
  The landed `RingedSpace.IsCoherent` is the exact notion and is reused.

Mismatch repaired: H8, the original proof docstring compressed the five node
steps and omitted their dependency references. Expanded it to the conventions,
the subsheaf argument, local finite-free presentation, local lifting onto the
kernel, and the finite-type-image/locality conclusion, with the nodes used.
No signature, hypothesis, conclusion, definition or DAG statement changed.
No new nodes or dependency modules are needed. The sole proof remains `sorry`;
there are no definitions in this delivery. Import, namespace, source tags and
100-character lines follow the conventions. The node's `lean.statement` already
equals the unchanged signature verbatim; every variable and universe is bound.
