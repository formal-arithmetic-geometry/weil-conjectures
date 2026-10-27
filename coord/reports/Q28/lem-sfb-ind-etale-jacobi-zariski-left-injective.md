## Worker report

The module `Sheaf.RingTheory.IndEtaleJacobiZariskiLeftInjective` states
`Algebra.jacobiZariski_left_injective_of_indEtale`, with its sole proof `sorry`.
There are no new definitions or auxiliary postponed theorems. The node is unchanged
except for its `lean` record.

I read Stacks `more-algebra.tex`, lemma-transitive-lci-at-end (07D4),
lemma-transitive-colimit-lci-at-end (07D5), and lemma-henselization-NL.
07D5 imposes no hypothesis on the first ring map. The last proof explicitly
uses the fact that etale algebras are local complete intersections.

Clause-by-clause correspondence:

- Commutative rings `A`, `B`, `C`: three independent universe binders `u v w`,
  three types, and their three `CommRing` instances. No nontriviality is required.
- The ring maps `A → B → C`, with the composite action on `C`: `[Algebra A B]`,
  `[Algebra B C]`, `[Algebra A C]`, and `[IsScalarTower A B C]`. These specify
  exactly a composable pair of ring maps and its composite, with `φ = algebraMap B C`.
  Commutativity makes every ring homomorphism an algebra structure.
- Ind-etaleness of the final map: `h : RingHom.IndEtaleAcrossUniverses
  (algebraMap B C)`, using the dependency's recorded predicate. Its canonical
  common-universe ULift transport avoids imposing an equality of ring universes.
- `I = ker(A[B] → B)`: `(Generators.self A B).toExtension.ker`.
  The self presentation has `val = id` and section `σ = MvPolynomial.X`.
- `I/I²`: `(Generators.self A B).toExtension.Cotangent`, Mathlib's conormal module.
- The free differential term and `δ`: the target and the map of
  `(Generators.self A B).toExtension.cotangentComplex`. Its target is
  `B ⊗[A[B]] Ω[A[B]/A]`, canonically free on all elements of `B` by
  `Generators.cotangentSpaceBasis`; `cotangentComplex_mk` is `[g] ↦ 1 ⊗ dg`,
  which in that basis is precisely the partial-derivative formula.
- Termwise tensoring: `.cotangentComplex.baseChange C` is the `C`-linear map
  `C ⊗[B] I/I² → C ⊗[B] CotangentSpace`. `LinearMap.baseChange_tmul`
  gives `c ⊗ z ↦ c ⊗ δ z`. Tensor symmetry identifies this with the node's
  tensor factor order `I/I² ⊗[B] C` and the corresponding degree-zero term.
- `H^{-1}` of that termwise tensor complex: the displayed `LinearMap.ker`
  of the base-changed differential. It is not replaced by tensoring `H^{-1}`.
- `J = ker(A[C] → C)`: the other self presentation. `H1Cotangent A C`
  abbreviates its differential kernel, so this is the node's `H^{-1}(NL_{C/A})`.
- The specific polynomial map `φ_sharp`: `Generators.defaultHom
  (Generators.self A B) (Generators.self A C)`, followed by `.toExtensionHom`.
  From the actual definitions, its value on `b` is `X (algebraMap B C b)`
  and it fixes coefficients in `A`. Thus it is exactly the specified map.
- The canonical conormal formula: `Extension.Cotangent.map` on that presentation
  homomorphism, followed by `.liftBaseChange C`. `Cotangent.map_mk` gives
  `[g] ↦ [φ_sharp(g)]`, and scalar extension gives `c ⊗ [g] ↦ c[φ_sharp(g)]`.
- Restriction to the two kernels, and `C`-linearity: the existential witness
  `f : LinearMap.ker (...) →ₗ[C] H1Cotangent A C` together with the universally
  quantified equation `h1Cotangentι (f x) = ... x.1`. This equation pins down the
  map uniquely because `h1Cotangentι` is the subtype inclusion. Consequently
  the witness is the canonical restriction, not a freely chosen injection.
- Injectivity is the final clause `Function.Injective f`.
- No locality, Noetherianity, or finite presentation of `A → B` appears anywhere
  in the signature. No flatness hypothesis is added either.

Statement dependency declarations read and used:

| Node | Module | Declaration used |
| --- | --- | --- |
| def-weil-pbc-ind-etale-algebra | Sheaf.RingTheory.IndEtaleUniverseTransport | RingHom.IndEtaleAcrossUniverses |
| def-weil-pbc-smooth-ring-map | Mathlib.RingTheory.Smooth.Basic; Mathlib.RingTheory.Extension.Cotangent.Basic | Algebra.Generators.self, Algebra.Extension.cotangentComplex, Algebra.H1Cotangent (the recorded smooth node explicitly identifies these as its naive-cotangent interface) |
| def-weil-pbc-module-tensor-product | Mathlib.LinearAlgebra.TensorProduct.Map (and TensorProduct.Tower, imported by the cotangent API) | TensorProduct, LinearMap.baseChange, LinearMap.liftBaseChange |

All three recorded dependency interfaces are usable; no dependency replacement
is needed. The theorem does not assume `Algebra.Smooth`: that node supplies the
standard naive cotangent complex, not a smoothness hypothesis.

Plain proof imports follow every currently stated proof dependency:
`Sheaf.RingTheory.ConormalIntersectionKoszulRegularIdeal`,
`Sheaf.RingTheory.SyntomicPolynomialKernelKoszulRegular`,
`WeilConjectures.RingTheory.ComposedConormalInjectiveOfIntersection`,
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties` and `Morphisms.Etale`,
`WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`,
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`, and
`Sheaf.RingTheory.PresentationsHomotopyEquivalent`.
Presentation H1 functoriality is in the publicly imported cotangent Basic module.
The locally missing ConormalIntersectionKoszulRegularIdeal source was read through
`scompile.py --source`, which returned the live declaration and docstring.
`lem-sfb-filtered-colimit-naive-cotangent-comparison` and
`lem-sfb-syntomic-smooth-composition` have no recorded Lean or Mathlib interface
at this reading and hence no proof import yet. They are not notions needed to
type this statement. Their intended uses remain explicit in the full four-step
proof docstring and in the unchanged DAG proof.

Edge cases checked mathematically before writing:

- `C` the zero ring: both relevant `C`-modules and the kernel vanish; the map
  and its injectivity are well-formed. No `Nontrivial C` excludes this case.
- `B → C` the identity: scalar extension identifies with the original module,
  the presentation homomorphism is the identity, and the restriction is the
  identity of the kernel.
- `A = B` with identity structure: the canonical polynomial presentation is
  still the self presentation, not incorrectly replaced by a zero conormal
  term. Its differential is split injective, so its kernel stays zero after
  termwise base change. The asserted injection remains valid.
- Arbitrary characteristic, non-Noetherian rings, infinite underlying generator
  sets, and independent ring universes are all admitted. There is no finite
  presentation binder on `A → B`, nor any filtered index restriction in the theorem.

Searches performed using `msearch.py` (results also in sandbox `searches.jsonl`):

- LeanFinder: `Jacobi Zariski injective first cotangent homology termwise tensor
  ind etale algebra canonical conormal map`. Eight hits, including
  `Extension.tensorH1Cotangent`, `h1Cotangentι_injective`, and
  `Generators.CotangentSpace.map_toComp_injective`. None states this theorem:
  a kernel inclusion or injection of the free term differs from this map;
  `tensorH1CotangentOfFormallyEtale` requires a formally etale map of presentation
  rings and a bijection on presentation ideals, not merely an ind-etale quotient map.
- Loogle: `"H1Cotangent", "injective"`. Two hits:
  `Algebra.Extension.h1Cotangentι_injective` and
  `Algebra.Extension.H1Cotangent.map_toExtendScalars_injective`; neither is this
  ind-etale, termwise-tensor canonical map.
- Mathlib grep: `IndEtale|indEtale|tensorH1Cotangent` in `RingTheory`.
  Eleven hits for flat base change and formally etale/localization comparisons;
  no ind-etale Jacobi-Zariski left-injectivity theorem.
- LeanSearch: `If B to C is ind etale then the canonical Jacobi Zariski map from
  the kernel of the base changed naive cotangent differential for B over A to
  H1Cotangent A C is injective`. Eight hits, including the localization-only
  `Generators.liftBaseChange_injective_of_isLocalizationAway`; no exact match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, for ind-etale/cotangent
  combinations, Jacobi-Zariski injectivity, and this exact node id. Found
  `WeilConjectures.RingTheory.JacobiZariskiRegularSequenceLeftInjective`, which
  requires a finite polynomial presentation with a globally regular sequence,
  and `Sheaf.RingTheory.IndEtaleNaiveCotangentAcyclic`, which concerns `NL_{C/B}`
  alone. Neither is this theorem. I read both full signatures and docstrings.
- Exact proposed declaration-name search in `dag/lean_names_upstream.json`,
  Mathlib, `WeilConjectures`, and `Sheaf` had no hits.

No statement correction, new node, dependency-interface fault, or
STATEMENT-DISPUTED flag is needed. The existential restriction formulation is
also used in the existing regular-sequence sibling theorem; this delivery
writes it without local `let` binders.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
