## Worker report

The module `Sheaf.AlgebraicGeometry.AdequatelyAffineComposition` states the two
clauses of `lem-sfb-adequately-affine-composition`, as
`CategoryTheory.adequatelyAffine_comp` and
`CategoryTheory.adequatelyAffine_of_affine`. Both proofs are `sorry`; no
construction, helper axiom, or additional definition is introduced.

Source checked directly: Alper, *Adequate moduli spaces and geometrically
reductive group schemes*, arXiv:1005.2398v3,
https://arxiv.org/html/1005.2398v3#S4.SS2, Proposition 4.2.1(1),(2), printed p.20.
Part (1) gives composition; the last sentence of part (2) gives affine examples.
The theorem docstrings carry the three DAG proof steps, including the important
point that f_*A → f_*B is universally adequate but need not be surjective.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `{k : Type u} [Field k]`, in both declarations. |
| U, V, W are algebraic stacks over k | `U`, `V`, `W` are `BasedCategory` over `Over (Spec (.of k))`; `hU`, `hV`, `hW` are the recorded `IsAlgebraicModuliStack` proofs. Each endpoint has independent object and morphism universes. The affine clause needs only U and V. |
| f : U → V and g : V → W are morphisms over k | `f : BasedFunctor U V` and `g : BasedFunctor V W`; these preserve the structural projection to schemes over k. |
| f and g are adequately affine | `hf : IsAdequatelyAffineMorphism f hU hV`, `hg : IsAdequatelyAffineMorphism g hV hW`. |
| g ∘ f is adequately affine | `IsAdequatelyAffineMorphism (f.comp g) hU hW`; `BasedFunctor.comp` composes the underlying functors in that order. |
| every affine morphism q : U → V | Arbitrary `q : BasedFunctor U V` with precisely the expanded affine hypothesis `hq`. |
| after every scheme test T → V | `∀ (T : Over (Spec (.of k))) (t : BasedFunctor (discreteModuli (yoneda.obj T)) V)`. The tests are all schemes over k, with no smoothness, affineness, or nonemptiness restriction. |
| the 2-fibre product is a scheme | Existential `P : Over (Spec (.of k))` and `e : BasedFunctor (discreteModuli (yoneda.obj P)) (moduliTwoFiberProduct t q)` with `e.toFunctor.IsEquivalence`. This preserves automorphisms; it is not a bijection of isomorphism classes. The order of the two factors is reversed from the prose only to use the existing first-projection interface. |
| its projection to T is affine | Existential `a : P ⟶ T`, `Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t q)) (discreteModuliMap (yoneda.map a)))`, and `IsAffineHom a.left`. The based 2-isomorphism identifies the actual projection with a, so an unrelated affine map cannot satisfy the hypothesis. Mathlib's class is defined by affine inverse images of every affine open. |
| q is adequately affine | `IsAdequatelyAffineMorphism q hU hV`. |
| no finite-type or characteristic condition | No such binder, nor Noetherian, diagonal, separatedness, or finite-generation hypothesis, occurs in either signature. The quasi-compact and quasi-separated conditions are conclusions inside the existing adequate-affineness predicate. |

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, line 180;
  it extends `CommRing` and `DivisionRing`.
- `def-sfb-algebraic-moduli-stack`:
  `CategoryTheory.IsAlgebraicModuliStack` in
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`. Read the full definition and
  its smooth-atlas predicates; it is stack descent, space-representable diagonal,
  and existence of a smooth surjective scheme atlas.
- `def-sfb-adequately-affine-morphism`:
  `CategoryTheory.IsAdequatelyAffineMorphism` in
  `Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism`. Read the entire module:
  qcqs plus universal positive-power lifting for all quasi-coherent algebra
  surjections. This is a public import, unchanged and not copied.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 42 and 74; read both docstrings and
  declarations. `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`, lines 44–48, gives exactly the
  affine-open inverse-image condition in the item's inline explanation.
- Existing underlying groupoid definitions, already public through the above
  dependencies, are `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, and `ModuliTwoIso` in
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`. Their full signatures
  and docstrings were read, along with `HasSpaceBaseChange` to check that the
  inline scheme presentation follows the existing projection convention.
  Mathlib's `BasedFunctor.comp` was also inspected.

The four proof-only dependency lemmas have no usable Lean record on the read
base, so there are no proof-only imports to add. Their mathematical steps are
retained verbatim in substance in the proof docstrings. No statement dependency
requires a repair, no new notion is needed, and only `lean` changes in the node.
The example CompactObject module has been withdrawn to an empty module; its
node record and the current module-mode instructions were read instead of
copying its obsolete format.

Edge cases checked before writing:

- Empty source stacks and empty scheme tests are permitted. The affine clause
  never asks for a point or a nonempty cover. The empty scheme may be P.
- Identity maps are included: their scheme test is represented by T and the
  projection is the identity affine morphism. No exclusion of isomorphisms.
- The affine property is substantial: a classifying stack of a nontrivial group
  over a scheme cannot have the required scheme presentation of every test,
  since the equivalence would have to retain its nontrivial automorphisms.
- Both characteristic zero and positive characteristic are permitted; no
  exponent, characteristic, degree, or finiteness bound is introduced.
- Source, intermediate, and target stack universes remain independent. Scheme
  tests and their representing schemes use the same base-scheme universe u,
  as in the recorded stack and adequate-affineness definitions. No independent
  smaller test universe or equality of endpoint universes is imposed.
- `set_option autoImplicit false` prevents auto-bound variables. Every theorem
  and universe is explicit. There is no file-local notation or instance.

Searches actually run, 2026-10-24:

- `msearch.py ... leanfinder`: “Adequately affine morphisms of algebraic stacks
  are closed under composition, and affine morphisms are adequately affine”.
  Eight hits, all ordinary scheme affineness statements (`IsAffineHom`, its
  multiplicativity, and related scheme property interfaces), no stack theorem.
- `msearch.py ... loogle`: `"Adequate", "Affine"`. Zero hits.
- `msearch.py ... grep`: `adequat|cohomologicallyAffine`. Nine unrelated
  occurrences of the English word “adequate”; no mathematical match.
- `msearch.py ... leansearch`: “An affine morphism of algebraic stacks is
  adequately affine; composition of adequately affine morphisms is adequately
  affine”. Eight hits, all scheme affineness; `IsAffineHom` itself was inspected
  and reused for the affine projection, not mistaken for a stack predicate.
- `rg -n -i 'adequately.?affine|cohomologically.?affine'` in both
  `lean/WeilConjectures` and `lean/Sheaf`: only the already recorded adequate
  definitions and references, no composition or affine-example theorem.
- `grep -rn 'lem-sfb-adequately-affine-composition' lean/WeilConjectures`:
  no occurrence. Direct searches for both proposed theorem names also gave no
  collision. Broader searches for affine `BasedFunctor`/moduli declarations
  found no existing predicate needed by the inline scheme-test hypothesis.

Validation: prescribed `scompile.py Q12 lem-sfb-adequately-affine-composition`
compiled the delivered module in both sandbox and library modes, with no errors
or non-sorry warnings (3.6 s and 3.3 s respectively). The only node-field change
is `lean`; the module's longest line is below 100 characters. Independent review
belongs to the maintainer under the current direct-delivery instructions.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
