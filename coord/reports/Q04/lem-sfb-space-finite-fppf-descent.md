## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteFppfDescent` states
`AlgebraicGeometry.AlgebraicSpace.finite_fppf_descent`. Its only proof is `sorry`.
The theorem is the fppf specialization of Stacks Tag 0426, with finiteness in the
scheme-test form of Tag 03ZQ. Both source passages were read locally, together
with the latest blueprint's direct-images proof. No statement correction,
new definition, or dependency repair is needed.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `universe u w` makes both universe
  parameters explicit. The size-convention node is metatheoretic and introduces
  no additional Lean object or assumption.
- `{X Y : AlgebraicSpace S}` and `(f : X ⟶ Y)` are exactly the two algebraic
  spaces over the given base and their natural transformation. This uses the
  existing full subcategory of fppf sheaves.
- Finiteness is `IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom`.
  Unfolding the existing predicate quantifies over EVERY `T : Over S` and
  EVERY map `yoneda.obj T ⟶ Y.obj.obj`, and supplies `U : Over S`, its scheme
  projection `p : U ⟶ T`, and a map to X forming an actual presheaf pullback
  square, together with `IsFinite p.left`. Thus the source of each test is
  represented by a scheme finite over T. There is no assumed representability
  of f: it is part of the conclusion on the left of the equivalence.
- The set-indexed family is `{I : Type w}`, `Yᵢ : I → AlgebraicSpace S`, and
  `g : ∀ i : I, Yᵢ i ⟶ Y`. No `Nonempty`, finite, or countable index restriction
  is imposed, and w is independent of the test-scheme universe.
- `hflat : ∀ i : I, MapIsFlat (g i)` uses the existing chartwise flatness
  definition. It tests all compatible representable etale scheme charts with
  the recorded Mathlib scheme property `Flat`.
- `hlfp : ∀ i : I, MapIsLocallyOfFinitePresentation (g i)` uses exactly the
  same existing chart tests with `LocallyOfFinitePresentation`.
- `hsurj : IsJointlySurjective (fun i : I ↦ (g i).hom.hom)` is the recorded
  point-class union-of-images condition, expressed by lifting a field-valued
  point after field extension. It is not objectwise surjectivity of sheaves.
- The conclusion is an `↔`, with the left scheme-test finiteness just described
  and, on the right, `∀ i : I` scheme-test finiteness of
  `(Limits.pullback.snd f.hom (g i).hom).hom`. This is the canonical projection
  `X ×_Y Yᵢ → Yᵢ` of SHEAVES. The recorded fibre-product closure theorem says
  that its source is an algebraic space. The predicate applies to the underlying
  presheaf morphism, so no additional choice of an algebraic-space representative
  or arbitrary comparison map occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`; its canonical
  sheaf pullback source and projection are used in the signature.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, through
  `MapIsFlat`; its full signature and stalkwise-equivalence docstring were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, through the chart predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsFlat`, `MapIsLocallyOfFinitePresentation`,
  and their common `MapIsLocally` definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`.

The last two owning definition nodes, `def-sfb-space-morphism-properties` and
`def-trf-algebraic-space-jointly-surjective-family`, are added to `stmt_deps`.
Both are existing landed definitions with usable interfaces. All original
statement dependencies, and all other node fields, are preserved.

The statement dependencies are public imports. Recorded proof dependencies
are plain imports: the four-property descent module, the open-subspace module,
the finite-affine-refinement module, Mathlib's scheme Limits/Affine/Separated
modules (coproducts, affine permanence and locality), and upstream FlatDescent
(`AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact`).
The fibre-product and finite scheme modules already occur as public imports.
`lem-sfb-space-largest-schematic-open` has no recorded Lean declaration/module;
it is retained in the proof plan and the theorem docstring, with no invented
import. It is not needed to type this statement. The complete six-step proof,
including the schematic-open representability argument, is in the docstring.

Edge cases checked before writing:

- I empty: joint surjectivity excludes every point of Y, so Y and X are empty;
  the right side is vacuous and the left is the finite empty scheme test.
- T empty and the zero-ring affine scheme: every scheme over T is empty, so
  the representability and scheme-finiteness tests hold. No nonzero-ring or
  nonempty-scheme assumption is introduced.
- Singleton identity covering: the equivalence is invariant under the canonical
  identity-pullback isomorphism and reduces to the same finite property.
- Arbitrary non-quasi-compact Y and covering members remain allowed. Only the
  proof's finite refinement over an affine test has a quasi-compact projection.
- A nonrepresentable f remains allowed as input: the theorem must establish
  representability from the local finite tests. No representability hypothesis
  was inserted.
- Scheme tests all have the base's universe u; there is no independently smaller
  test universe that could make the finiteness condition vacuous.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A finite morphism of algebraic spaces descends
  along jointly surjective flat locally finitely presented families"`: eight
  hits, including scheme FlatDescent results, IsFinite and
  LocallyOfFinitePresentation; none states this algebraic-space theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite"`: twelve hits in
  Mathlib's Finite module: scheme finiteness, permanence and equivalent scheme
  predicates, not algebraic-space descent.
- `msearch.py ... leansearch "Finiteness of a morphism of algebraic spaces is
  local for a jointly surjective flat locally finitely presented covering
  family"`: eight hits; scheme IsFinite and basic scheme covering and lfp
  declarations only.
- `msearch.py ... grep "IsFinite|finite.*descen" AlgebraicGeometry`: twenty-five
  hits, all scheme-level results. Read the finite scheme definition and its
  base-change instance, and the upstream fpqc-descent declaration/docstring.
- `rg -n 'IsRepresentableWith.*IsFinite|finite_fppf|MapIsFinite|finite.*descent|finite.*fppf'
  lean/WeilConjectures lean/Sheaf/AlgebraicGeometry`: existing relative-Spec
  and module direct-image statements use the same scheme-test predicate;
  no existing theorem gives this descent equivalence.
- `rg -n 'lem-sfb-space-finite-fppf-descent' lean/WeilConjectures`: no match.
- Exact proposed name searches in both Lean source roots and
  `dag/lean_names_upstream.json`: no declaration clash.

Validation: the prescribed `scompile.py Q04 lem-sfb-space-finite-fppf-descent`
compiled the delivered module in sandbox and library modes, each in 1.7 seconds,
with no errors or warnings. No local or global build was run. No disputed
statement or node fault was found.

## Second reading by Q04

Worker self-audit, not an independent-agent review: re-read the node alongside
its Lean signature after compilation. The base and morphisms, arbitrary family,
three covering hypotheses, two finite scheme-test clauses, and sheaf pullback
projection match in the order recorded above. In particular the second projection
has target Yᵢ, not X, and no preexisting representability assumption is used.
The only DAG additions are the two owning definition-node references described
above. The proof docstring retains the representability step repaired by the
stage-1 reviewer. No mismatch was found or statement changed. The dispatcher
forbids starting other agents; the maintainer provides the independent review
of this delivery as specified in the worker brief.
