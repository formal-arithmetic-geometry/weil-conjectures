## Worker report

The module `Sheaf.RingTheory.CyclicExtensionFlatDescent` states
`LinearMap.exists_cyclic_extension_flat_descent`. Its only theorem has proof `by sorry`;
there are no new definitions or dependency modules. The node is changed only in `lean`.

Hypothesis and conclusion correspondence:

- The commutative rings are `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  `[Algebra R S]` supplies exactly the ring map in the node, namely `algebraMap R S`.
  Every ring map φ is represented by `φ.toAlgebra`; this adds no restriction on φ.
- Flatness of that map is `_hflat : (algebraMap R S).Flat`, using `RingHom.Flat`.
- The ideal and its finite generation are `(I : Ideal R) (_hI : I.FG)`.
- The canonical map R/I → S/IS is `Ideal.quotientMap (I.map (algebraMap R S))
  (algebraMap R S) Ideal.le_comap_map`; `_hquot : Function.Bijective ...` says
  precisely that this ring homomorphism is an isomorphism. `I.map` is the extended
  ideal IS, and the existing lemma `Ideal.le_comap_map` supplies well-definedness.
- `(n : ℕ) (_hn : 1 ≤ n)` renders n ≥ 1, with no assumption n = 1.
- `{N : Type w} [AddCommGroup N] [Module R N]` is the arbitrary R-module.
- C is the actual quotient `R ⧸ I ^ n`. Its scalar extension C_S is
  `S ⊗[R] (R ⧸ I ^ n)`, and N_S is `S ⊗[R] N`. The dependency explicitly permits
  this tensor-factor convention, identified with M ⊗_R S by tensor symmetry.
- `{T : Type x} [AddCommGroup T] [Module S T]` and the S-linear maps `a`, `b`
  supply the given middle term, injection and projection. The three hypotheses
  `_ha : Function.Injective a`, `_hab : Function.Exact a b`, and
  `_hb : Function.Surjective b` render exactness at all three nonzero terms.
  `Function.Exact` also implies the composite is zero; no complex hypothesis is missing.
- The conclusion existentially binds E, its additive group and R-module structures,
  and `j : N →ₗ[R] E`, `q : E →ₗ[R] (R ⧸ I ^ n)`. The conjunction of injectivity,
  exactness and surjectivity is exactly the requested R-short exact sequence.
- `θ : S ⊗[R] E ≃ₗ[S] T` is the requested S-linear isomorphism. The equalities
  `θ.toLinearMap.comp (j.baseChange S) = a` and
  `b.comp θ.toLinearMap = q.baseChange S` state both commuting squares, including
  the fixed end maps and the fixed quotient, rather than merely an isomorphism of middle terms.

Dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`;
  its definition installs the algebra structure of the map and asserts `Module.Flat R S`.
  The Module.Flat signature and docstring in `Mathlib.RingTheory.Flat.Basic` were read too.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `LinearMap.baseChange`, with its full signature and tensor formula. No private scalar-extension
  definition is introduced.
- `def-weil-pbc-exact-sequence`: the recorded `CategoryTheory.ShortComplex.ShortExact`
  (exact, mono, epi). In modules its concrete interpretation is injective / Function.Exact /
  surjective, used inline without defining another predicate. The imported
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` supplies
  `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
  `ShortExact.moduleCat_injective_f`, and `ShortExact.moduleCat_surjective_g`.
  Their signatures, together with the ShortExact structure and `LinearMap.exact_iff`,
  were read. This is the same notion, expressed concretely to allow independent universes
  for the three modules; no replacement definition or specialization node is required.

Edge cases checked before writing:

- I = 0: C = R, and the residue-isomorphism condition makes φ an isomorphism;
  extensions of the free cyclic quotient descend. The proof can use a zero generator.
- I = R: C = 0, and an extension of zero has middle term isomorphic to N_S;
  E = N with identity injection and zero projection works, without faithful flatness.
- N = 0, T = 0 when allowed, the zero ring, n = 1, and every characteristic are permitted.
  No nontriviality, Noetherian or finite-module assumption is imposed.
- R, S, N and T have independent universes u, v, w, x. E lives in `Type (max u w)`:
  the constructive model is a quotient of N × R, so this existence bound excludes no case.
  S and T need not live in E's universe. No variable or universe is auto-bound.

Source check: the local literature checkout is not present on this machine, so the source was
read directly at https://stacks.math.columbia.edu/tag/05EG (Lemma 15.91.8), particularly its
second proof paragraph for M = R/I^n. It agrees with the node. The docstring carries all nine
node proof steps, with the cocycle construction, torsion comparisons, and both commuting squares.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches for an existing statement (all service searches were made through msearch.py):

- LeanFinder: "Extensions of R/I^n by N descend along a flat ring map inducing an
  isomorphism modulo I". Eight results concern formal smoothness and adic completion;
  none states descent of module extensions.
- Loogle: "Module.Flat, CategoryTheory.ShortComplex.ShortExact". Zero hits.
- Mathlib grep: "neighbourhood.*extension|cyclic.*descent|extension.*flat" under
  RingTheory. Four hits on base change of cotangent modules, none a match.
- LeanSearch: "A short exact extension of S tensor R/I^n by S tensor N descends to R
  when R to S is flat and an isomorphism modulo I". Service unavailable (Internal Server
  Error), recorded as unavailable, not as evidence of absence. LeanFinder, Loogle and
  source grep provided the other searches.
- rg of WeilConjectures and lean/Sheaf for the item id,
  `neighbourhood.extensions`, and `cyclic.*[Dd]escent`: no existing declaration.
  The full proposed declaration name was also searched in Mathlib, WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json, without a name collision.

Validation: scompile.py compiled the module on the server in 1.7 seconds with exit code 0
and no warnings. Delivery dry run is the final worker check; the independent second reader
writes its own section and performs delivery.

## Second reading by G1

I independently read the base node, the sandbox node and module, all three statement
 dependency nodes, and their Mathlib declarations. Verdict: the Lean says exactly what
 the node says; no mathematical or signature repair is needed. There are no new nodes,
 dependency modules, or statement corrections in this delivery.

Source: I read [Stacks 05EG](https://stacks.math.columbia.edu/tag/05EG) and the raw
`more-algebra.tex` at `lemma-neighbourhood-extensions`, including the preceding
`section-formal-glueing` introduction. The local checkout contains citation lists but
not that source file. The cyclic specialization of the lemma and its Ext comparison
proof agree with the node. The section's introductory Noetherian scheme motivation
is not an extra hypothesis on the rings of this self-contained lemma.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Arbitrary commutative rings R and S and a ring homomorphism φ: the independent
   `Type u`, `Type v`, `[CommRing R]`, `[CommRing S]`, and `[Algebra R S]` give
   `φ = algebraMap R S`. Any unital ring homomorphism gives this algebra through
   `φ.toAlgebra`; no algebraic finiteness or injectivity assumption is added. Pass.
2. φ flat: `_hflat : (algebraMap R S).Flat`. I opened `RingHom.Flat` in
   `Mathlib.RingTheory.RingHom.Flat`: it installs `f.toAlgebra` and asserts
   `Module.Flat R S`; `flat_algebraMap_iff` identifies this with the current
   algebra structure. This is exactly `def-weil-pbc-flat-ring-map`. Pass.
3. Ideal I, finitely generated: `(I : Ideal R) (_hI : I.FG)`. Pass.
4. The induced R/I → S/IS is an isomorphism: `_hquot` is bijectivity of
   `Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
   Ideal.le_comap_map`. I read `quotientMap` and `quotientMap_mk` in
   `Mathlib.RingTheory.Ideal.Quotient.Operations`: this sends the class of r
   to the class of φ(r). Bijectivity of this ring hom is exactly the required
   isomorphism, rather than an arbitrary isomorphism of the quotient rings. Pass.
5. Positive integer n: `(n : ℕ) (_hn : 1 ≤ n)`. Arbitrary R-module N:
   `{N : Type w} [AddCommGroup N] [Module R N]`. Pass.
6. C = R/I^n and its scalar extension: the actual quotient `R ⧸ I ^ n` and
   `S ⊗[R] (R ⧸ I ^ n)`. Likewise N_S is `S ⊗[R] N`. I read
   `def-weil-module-base-change` in sec-smooth-purity and `LinearMap.baseChange`
   with its surrounding variables and `baseChange_tmul` in TensorProduct.Tower.
   That dependency expressly records this tensor order via tensor symmetry, so
   the change of order is already the project's shared notion. Pass.
7. Every given S-extension, including its fixed maps: arbitrary T in `Type x`
   with `[AddCommGroup T] [Module S T]`, and S-linear `a` and `b`, followed
   by `_ha : Function.Injective a`, `_hab : Function.Exact a b`, and
   `_hb : Function.Surjective b`. I read `ShortComplex.ShortExact` and the
   ModuleCat exactness, injection and surjection lemmas named in the worker
   report, as well as `LinearMap.exact_iff`. The conjunction is precisely short
   exactness; equality of image and kernel implies b ∘ a = 0. The concrete
   rendering is not a new definition of `def-weil-pbc-exact-sequence`. Pass.
8. An R-extension of the same fixed N and C: existential E, its additive group
   and R-module structures, j and q with the same three exactness conditions.
   The existential follows all data of the given extension, as required. Pass.
9. An S-linear isomorphism of extensions: `∃ θ : S ⊗[R] E ≃ₗ[S] T`,
   with `θ.toLinearMap.comp (j.baseChange S) = a` and
   `b.comp θ.toLinearMap = q.baseChange S`. Both end maps are fixed, both
   commuting squares are present, and the equivalence is S-linear. Pass.

Edge cases: n = 0 is excluded exactly by the node's n ≥ 1, while n = 1 is
included. I = 0, I = ⊤, the zero ring, and N = 0 are not excluded; if T = 0
is compatible with exactness it is also included. For I = ⊤ the quotient is
zero and descent can take E = N. For I = 0 the residue hypothesis makes φ
itself an isomorphism. There is no generator index set in the statement; the
empty choice of generators of the zero ideal causes no statement restriction
(the documented proof permits an extra zero generator). There are no schemes,
so empty-scheme cases are inapplicable. All characteristics are allowed.
Independent universes u, v, w, x cover all rings and input modules. E in
`Type (max u w)` suffices because the node's construction is a quotient of
N × R, so the universe bound excludes no existence case. All variables and
universes are explicitly bound.

Independent searches (different wording from the first reader):

- LeanFinder through msearch.py: "Descent of short exact module sequences with
  cyclic quotient under flat residue isomorphism". Eight hits: ModuleCat
  exactness, flatness criteria/factorizations, and quotient exactness; none is
  this descent theorem.
- Loogle through msearch.py: `Function.Exact, LinearMap.baseChange`. Zero hits.
- LeanSearch through msearch.py: "Every extension of a scalar extended ideal
  power quotient descends along a flat homomorphism with isomorphic residue
  quotients". Service unavailable (Internal Server Error); no absence verdict
  is inferred from this failure.
- rg over Mathlib, WeilConjectures, and lean/Sheaf for extension/descent,
  extension/residue, cyclic/extension, neighbourhood/extension, 05EG and its
  source label: unrelated topology, number theory, and sheaf descent hits;
  none states the lemma. The exact proposed declaration name and item id have
  no declaration match in the source libraries or upstream name index.

H5/H6/H8/H9: there are no definitions with postponed data, no private notion,
and only one theorem, whose entire proof is `by sorry`. Its docstring carries
all nine node proof steps in order, including admissibility and both squares,
with the Stacks source and blueprint id. Namespace, topic path, imports, and
line widths satisfy the brief. The ModuleCat import is used by the explicit
short-exactness interpretation documented in the module. The sandbox node's
`lean.statement` matches the complete signature verbatim, without the proof.

Mismatches and changes: none found. I left the Lean and node unchanged and
appended this independent reading. Validation: scompile.py on the sole module
returned exit code 0, compiled in 1.6 seconds, with no warnings or errors.
