## Worker report

The module `Sheaf.RingTheory.FinitePresentationKerRangeCokernel` states
`Module.finitePresentation_ker_range_cokernel_of_fg_ideals`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.

The correspondence to the node is clause by clause:

- “R a commutative ring”: `{R : Type u} [CommRing R]`.
- “Every finitely generated ideal of R is finitely presented”:
  `hR : ∀ (I : Ideal R), I.FG → Module.FinitePresentation R I`.
  Here `I` is the ideal itself as an R-module, not the quotient ring R/I.
- “M and N are R-modules”: `{M : Type v} {N : Type w}` with
  `[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]`.
- “M and N are finitely presented”: `[Module.FinitePresentation R M]` and
  `[Module.FinitePresentation R N]`.
- “f is R-linear”: `(f : M →ₗ[R] N)`.
- “Ker(f) is finitely presented”: `Module.FinitePresentation R (LinearMap.ker f)`.
- “Im(f) is finitely presented”: `Module.FinitePresentation R (LinearMap.range f)`.
- “Coker(f) is finitely presented”: `Module.FinitePresentation R (N ⧸ LinearMap.range f)`.
  The quotient by the image is the ordinary module cokernel, with its standard R-action.
  The conjunction asserts all three conclusions for the same map.

Dependency: `def-sc-finitely-presented-module` is a Mathlib leaf. Its `mathlib_match` is
`Module.FinitePresentation` in `Mathlib.Algebra.Module.FinitePresentation`. I read the full
class signature and docstring (lines 62–69), and `Module.FinitePresentation.exists_fin'`,
which expresses its equivalent finite-free right exact presentation. The match is usable
without any dependency module. Mathlib's `Ideal`, `Ideal.FG`, `LinearMap.ker`,
`LinearMap.range`, and `Submodule.Quotient` supply the remaining ordinary algebraic objects.
The file imports finite presentation and ideals; it adds no coherence definition, instead
writing the hypothesis verbatim as a proposition about ideals.

Source checked: the local Stacks algebra.tex is absent on this machine, so I opened the
primary Stacks pages https://stacks.math.columbia.edu/tag/05CU,
https://stacks.math.columbia.edu/tag/05CW, and https://stacks.math.columbia.edu/tag/05CX.
They agree with the node: the ideal condition is coherence, and finitely presented modules
are coherent over such a ring; the kernel, image, and cokernel closure follows. The
three-step proof in the declaration docstring reproduces the node's argument. No node
fault or disputed statement was found.

Edge cases checked before writing: the zero ring is allowed (no Nontrivial assumption);
zero modules and zero maps are allowed, giving kernel M, zero image, and cokernel N;
the identity gives zero kernel, full image, and zero cokernel. Non-Noetherian coherent rings
are included, with no Noetherian or domain assumption. All ring and module universes are
explicit and independent (`u v w`), and no finiteness of the ambient types is assumed.
The zero ideal and unit ideal are included in the ideal hypothesis.

Searches made (logged by msearch.py in searches.jsonl):

- LeanFinder: “kernels images and cokernels of linear maps between finitely presented
  modules over a coherent commutative ring are finitely presented”: eight hits, including
  `Module.FinitePresentation.fg_ker`, `Module.finitePresentation_of_ker`,
  `Module.finitePresentation_of_surjective`, and `Module.Presentation.ofExact`.
  These concern different hypotheses or only parts of the conclusion, not this statement.
- Loogle: `Module.FinitePresentation, LinearMap.ker`: seven hits, including the class's
  fields and finite-presentation lemmas for surjections; no coherent-ring closure result.
- Mathlib grep via msearch.py:
  `coherent|FinitePresentation.*(ker|range)|finitePresentation.*(ker|range)` in Algebra/Module:
  six hits, all ordinary finite-presentation lemmas, not the item.
- LeanSearch: “over a coherent ring the kernel image and cokernel of a map of finitely
  presented modules are finitely presented”: service unavailable (Internal Server Error).
- Direct rg on WeilConjectures and lean/Sheaf for
  `finitePresentation.*(ker|range)|FinitePresentation.*(ker|range)|every finitely generated ideal|coherent ring`:
  found scheme/Noetherian results and uses of the surjective presentation lemmas, no match.
- Direct grep for the item's blueprint id in WeilConjectures: no occurrence.
- Name collision search for `finitePresentation_ker_range_cokernel_of` and
  `finitePresentation.*coherent` in dag/lean_names_upstream.json, Mathlib,
  WeilConjectures, and lean/Sheaf: no occurrence.

Validation: remote single-file compilation via scompile.py; final delivery dry run via
`deliver2.py G1 lem-sc-coherent-ring-fp-kernel-cokernel --no-push`.

## Second reading by G1

I independently opened the sandbox node and Lean module, the dependency node
`dag/nodes/sec-picard-framework/def-sc-finitely-presented-module.json`, and Mathlib's
`Algebra/Module/FinitePresentation.lean`. The complete object/hypothesis/conclusion
list of the node, with its Lean rendering and verdict, is:

- Object R, a commutative ring with identity: `{R : Type u} [CommRing R]`. Exact.
- Hypothesis on every ideal I of R: `(hR : ∀ (I : Ideal R), I.FG →
  Module.FinitePresentation R I)`. `Ideal` is the ordinary submodule of R, and `FG`
  means finitely generated as a submodule. The finite-presentation predicate is
  applied to I's carrier with its inherited R-action, not R/I. Exact.
- Objects M and N, R-modules: `{M : Type v} {N : Type w}` and the four instances
  `[AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]`. Exact.
- Hypotheses that both modules are finitely presented:
  `[Module.FinitePresentation R M] [Module.FinitePresentation R N]`. These are
  proposition-valued class hypotheses, introducing no additional chosen data. Exact.
- Object f, an R-linear map from M to N: `(f : M →ₗ[R] N)`. Exact; no injectivity,
  surjectivity, or condition on its image is assumed.
- Conclusion that its kernel is finitely presented:
  `Module.FinitePresentation R (LinearMap.ker f)`. Exact.
- Conclusion that its image is finitely presented:
  `Module.FinitePresentation R (LinearMap.range f)`. Exact.
- Conclusion that its cokernel is finitely presented:
  `Module.FinitePresentation R (N ⧸ LinearMap.range f)`. This is the ordinary module
  quotient by the image with its induced action, hence the module cokernel. Exact.
- The conclusions are conjoined for the same universally quantified R, M, N and f;
  all hypotheses precede them. No hypothesis or conclusion is added or omitted.

The source checkout lacks the local Stacks algebra.tex, so I fetched the primary
[Stacks algebra.tex](https://github.com/stacks/stacks-project/blob/master/algebra.tex)
into the sandbox for reading. I read its Conventions (rings are commutative with 1,
and the zero ring is included), and the full section `section-coherent`, particularly
`definition-coherent`, `lemma-coherent`, and `lemma-coherent-ring`. The associated
primary pages [05CU](https://stacks.math.columbia.edu/tag/05CU),
[05CW](https://stacks.math.columbia.edu/tag/05CW), and
[05CX](https://stacks.math.columbia.edu/tag/05CX) confirm the tag/label correspondence.
The ideal hypothesis is exactly coherence, and passage between coherent and finitely
presented modules gives all three clauses. No ambient Noetherian, domain, field,
characteristic, or nontriviality assumption is present in the source.

The dependency's Mathlib record is usable: `Module.FinitePresentation` is a Prop
class whose data is a finite generating set with finitely generated relation kernel.
I also read `Module.FinitePresentation.exists_fin` and `exists_fin'`; their explicit
finite-free presentations agree with the dependency's exact sequence definition.
The statement uses this declaration throughout. No new definition node, dependency
module, or statement correction occurs in this delivery.

Edge cases: the zero ring and zero modules are permitted; every module over the zero
ring is necessarily zero, without requiring a `Nontrivial` instance. The zero map
has kernel M, image zero, and quotient N; the identity has kernel zero, image M, and
zero quotient. Zero and unit ideals are both quantified by hR. Empty generating
sets and presentations of rank n = 0 are allowed by Mathlib's Finset/Fin formulation.
There is no characteristic restriction or scheme object (so an empty scheme is not
an input here). The explicitly bound independent universes u, v, w impose no
Small or common-universe condition; all variables are explicitly bound.

Independent searches, using different wording from the first reading:

- LeanFinder via msearch.py: "A commutative coherent ring has finitely presented
  submodules for finitely generated submodules of finitely presented modules".
  Eight hits: finite presentation definitions/presentations, Noetherian equivalences,
  and finite algebra/module comparisons; no match to this closure statement.
- Loogle via msearch.py: `Module.FinitePresentation, LinearMap.range`: zero hits.
- LeanSearch via msearch.py: "Finitely presented modules form an abelian category
  when all finitely generated ideals are finitely presented": service unavailable
  (Internal Server Error), recorded as unavailable rather than a negative result.
- Direct rg of Mathlib RingTheory and Algebra/Module for `coherent|Coherent`:
  only an unrelated quasi-coherent-sheaf comment in Grassmannian. No coherent-ring
  predicate or closure theorem. Read the finite-presentation module's declarations.
- Direct rg of WeilConjectures and lean/Sheaf for finite-presentation kernel/range
  names and "finitely ... presented ... kernel/image/cokernel": the closest theorem
  is `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`. I opened its
  signature: it concerns sheaf modules on a locally Noetherian scheme, so it does
  not match these module objects or hypotheses. FiniteDescent's cokernel argument
  supplies only the quotient clause, not the coherent-ring closure theorem.
- Direct name search in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no collision with the new declaration.

No mismatch was found, and no Lean or node change was needed. The module and theorem
docstrings name the source and blueprint id; the theorem docstring reproduces all
three node proof steps, including the finite-free coherence argument and the quotient
presentation construction. There are no definitions, no hollow data, and no proved
theorems: the only proof is `sorry`. Both imports supply notions used in the signature.
The node's lean.statement is verbatim the signature before `:=`, and every source
line is within 100 characters. Validation is by the remote single-file compile and
delivery dry run recorded below.

Second-reader validation: scompile.py exited 0 (compiled in 1.3 s, no warnings).
The signature comparison returned True; no Lean line exceeds 100 characters.
The delivery dry run printed OK: preflight passed and compilation passed.
