## Worker report

Item: lem-sfb-separated-source-finite-inertia-target. The module
`Sheaf.AlgebraicGeometry.SeparatedSourceFiniteInertiaTarget` states all three
assertions as three named theorems, each with proof `sorry`:
`CategoryTheory.stack_separated_source_finite_inertia_target`,
`CategoryTheory.stack_separated_of_comp_diagonal_separated`, and
`CategoryTheory.stack_diagonal_separated_of_inertia_separated`.
Nothing is proved or defined in this delivery. The existing node changes only in
`lean`; there are no new nodes, dependency repairs, or statement corrections.

I read Stacks `stacks-morphisms.tex`, lemma-compose-after-separated (Tag 050M),
part (3) and its proof, and lemma-diagonal-diagonal (Tag 0CL0), part (1), with the
preceding identification of the second diagonal and the neutral section. I also
read the final separatedness argument of lemma-etale-local-finite-inertia
(Tag 0DUE) in `stacks-more-morphisms.tex`. These agree with the node. The proof
of 050M(3) has the already reported typo “quasi-separated” in the sentence that
uses properness of A → T; its actual hypothesis, its statement, and our hypothesis
are separatedness. No statement correction is needed.

Hypotheses and clauses, in order:

- The base field is `(k : Type u) [Field k]`, and every stack is a
  `BasedCategory` over `Over (Spec (.of k))`. Morphisms are `BasedFunctor`, hence
  functors over precisely this base, with no additional representability condition.
- The explicit universes are `u v₁ w₁ v₂ w₂ v₃ w₃`. Stack object and morphism
  universes are independent; the scheme universe is the same `u` as the field
  and the existing algebraic-space framework. `set_option autoImplicit false`
  rules out inferred undeclared variables.
- `hA`, `hB`, and (in cancellation) `hC` are the existing
  `IsAlgebraicModuliStack` predicates. They retain etale stack descent,
  algebraic-space diagonal and a smooth surjective scheme atlas. No
  Deligne–Mumford, noetherian, finite-type, or chosen-atlas assumption is added.
- Properness of a representable stack map `d` is rendered directly as: for every
  scheme `T` and map `t` to the target of `d`, there exist an algebraic space `Z`
  and its projection `p : Z.obj.obj ⟶ yoneda.obj T`, with
  `HasSpaceBaseChange d T t Z p` and
  `AlgebraicSpace.MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T)`.
  `HasSpaceBaseChange` retains an equivalence of the actual 2-fibre product and
  the projection comparison over T. The bundled map has exactly underlying
  presheaf map p; the expression does not introduce an arbitrary map.
  `MapIsProper` is the existing separated, finite-type, universally-closed
  algebraic-space predicate. Local finite type is tested on compatible etale
  charts; universal closedness uses all algebraic-space base changes and their
  existing atlas point topology. A proper space is not required to be a scheme.
- “A is separated over k” is `hAsep`: the preceding properness test applied to
  `moduliRelativeDiagonal (moduliBaseStructure A)`, whose target is the actual
  `moduliTwoFiberProduct (moduliBaseStructure A) (moduliBaseStructure A)`.
- Inertia is the existing `moduliInertia B` and `moduliInertiaProjection B`:
  objects retain a vertical automorphism; arrows commute with the automorphisms,
  hence are the conjugating isomorphisms in each groupoid fibre.
- Finite inertia is exactly
  `hI : IsRepresentableFiniteModuliMap (moduliInertiaProjection B)`. The existing
  predicate quantifies over every scheme base change and gives a finite scheme
  projection, an equivalence with that fibre product, and its projection comparison.
  Flatness, reducedness, and etaleness of inertia are not assumed.
- The first conclusion is the properness test for `moduliRelativeDiagonal f`,
  over its true target `moduliTwoFiberProduct f f`. This is precisely separatedness
  of the arbitrary k-morphism f, with no properness hypothesis on f or separatedness
  hypothesis on B.
- The second theorem states the “more generally” clause. `f : BasedFunctor A B`
  and `g : BasedFunctor B C` are arbitrary. `hcomp` is properness of
  `moduliRelativeDiagonal (f.comp g)`. `hdiag` is properness of
  `moduliRelativeDiagonal (moduliRelativeDiagonal g)`, namely separatedness of
  the diagonal of g, not separatedness or properness of g itself. The conclusion
  is again properness of `moduliRelativeDiagonal f`.
- The third theorem states the final implication. `hIsep` is properness of the
  relative diagonal of `moduliInertiaProjection B`, namely separated inertia.
  Its conclusion is properness of
  `moduliRelativeDiagonal (moduliRelativeDiagonal (moduliBaseStructure B))`,
  namely separatedness of the structural diagonal of B. This theorem does not
  assume finite inertia and does not assert that B itself is separated.
- The node's point-space, flatness, local finite presentation, and etaleness
  conventions supply background meanings. Their existing declarations are
  imported through the recorded modules; there is no additional point-space or
  flatness conclusion in this node. The module does not replace these notions.

Declarations read and used (including the shared canonical constructions):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.moduliTwoFiberProduct`, `discreteModuli`, `BasedFunctor`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`, `IsModuliStack` and
  `HasAlgebraicSpaceDiagonal`. The categories/functors over the base come from
  the imported Mathlib framework. The stable-family specialization is not used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsEtale` and
  `AlgebraicSpace.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.moduliRelativeDiagonal`. Its definition is general; its
  module name imposes no DM hypothesis. I specifically did not use the
  DM-oriented `ModuliSchemeTest @IsProper` or `HasProperModuliDiagonal` as
  separatedness for arbitrary algebraic stacks.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`:
  `CategoryTheory.moduliBaseStructure`; `Sheaf.AlgebraicGeometry.ModuliInertia`:
  `ModuliInertiaObject`, `moduliInertia`, `moduliInertiaProjection`.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `CategoryTheory.IsRepresentableFiniteModuliMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsProper`, with `MapIsSeparated`,
  `MapIsFiniteType`, `MapIsLocally`, and `MapIsUniversallyClosed` read to check
  its mathematical meaning.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace` (the actual representable sheaf).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `FinitePresentation`, `Etale`,
  `Proper`, and `Finite` supply the recorded `AlgebraicGeometry.Flat`,
  `LocallyOfFinitePresentation`, `Etale`, `IsProper`, and `IsFinite` conventions.
  I read their signatures and docstrings. The finite-implies-proper input is
  `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom` in `Proper`.
- `Sheaf.AlgebraicGeometry.StackPointTopology`:
  `CategoryTheory.stack_point_topology`, retaining the recorded point convention.
- Stated proof dependencies imported non-publicly:
  `Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts`
  (`CategoryTheory.algebraicStack_twoFiberProduct`),
  `Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry`
  (`CategoryTheory.relative_inertia_second_diagonal_geometry` and
  `relative_moduli_inertia_absolute`),
  `Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus`
  (`CategoryTheory.stack_closedImmersion_baseChange` and companion clauses),
  and `Mathlib.AlgebraicGeometry.Morphisms.Proper` (finite iff proper and affine).
  The other proof dependency nodes have no recorded Lean declaration at the
  checked base: fibred-groupoid representable-smooth calculus, stack separation
  permanence, space proper cancellation, space proper base change and closed
  subspace properness. Their IDs remain in the node and in the proof docstrings;
  there is no unavailable-module import or fabricated replacement theorem.

Edge cases checked before writing:

- Empty stacks and empty scheme tests are allowed; no nonemptiness binder was
  introduced. Empty algebraic spaces remain valid proper test projections.
- Identity f: the relative diagonal is the identity up to its canonical
  equivalence, so both the finite-inertia result and cancellation specialize
  correctly. Taking g to be the identity makes the second assumption harmless.
- For schemes, inertia is the identity. The first theorem specializes to the
  usual statement that a map from a separated k-scheme is separated.
- For BG, inertia is [G/G]. Finite nonreduced stabilizers such as μ_p in
  characteristic p are allowed. No etaleness or DM property is imposed.
- Proper nonfinite stabilizers are allowed in the general cancellation and
  separated-inertia clauses; hence those tests cannot be changed to finite
  tests. A nonproper group such as G_m makes BG fail the source separatedness
  hypothesis, as it should, rather than providing a counterexample.
- The separated-inertia implication asserts only separatedness of the diagonal;
  it does not conclude separatedness of BG. This distinction is necessary.
- No characteristic, dimension, finite-presentation or index-set restriction
  occurs. Separate stack universes and all k-scheme tests are retained.

Searches performed on 2026-10-24:

1. `msearch.py ... leanfinder` query “A morphism from a separated algebraic stack
   to an algebraic stack with finite inertia is separated”: eight hits, including
   `AlgebraicGeometry.IsFinite.instHasOfPostcompPropertySchemeIsSeparated`,
   `AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated`, and
   `AlgebraicGeometry.IsSeparated.hasAffineProperty`. They concern schemes,
   and none states this three-clause algebraic-stack result.
2. `msearch.py ... loogle '"IsSeparated", "inertia"'`: zero hits.
3. `msearch.py ... grep 'stack.*separat|separat.*inertia|proper.*stack'
   AlgebraicGeometry`: zero hits in Mathlib.
4. `rg` in `lean/WeilConjectures` for the item ID and for separated/inertia
   combinations: no matching declaration. `rg` in `lean/Sheaf` for the item ID,
   the proposed theorem names and separated-source patterns: no existing theorem.
   Broader searches for inertia, diagonals, separatedness and finite stack maps
   found and were used to read the shared modules listed above.
5. DAG searches found `lem-sfb-stack-inertia-separated-diagonal` and
   `lem-sfb-stack-separated-source-separated-inertia-target`; I read their
   statements and checked their records. These are DM-only results, the latter
   with absolute source separatedness, so they do not state the item. They have
   no usable existing theorem to reuse for this general statement.

The final `scompile.py Q135 lem-sfb-separated-source-finite-inertia-target <file>`
compiled both sandbox and library module without errors or warnings (3.4 s and
3.5 s reported). The first compile found a single long line; it was wrapped and
this final compile was clean. All three theorem bodies are `by sorry` and all
three belong to this node and are listed in `lean.declarations`.

## Second reading by Q135

Final rereading by the same worker (the dispatcher explicitly prohibits spawning
other agents); the maintainer's independent review remains the independent
reading. I reread the node and final file together. Each of the three assertions
is present: finite-inertia target, cancellation, and the separated-inertia
implication. `hAsep` uses the structural diagonal, the first two conclusions
use the diagonal of f, `hdiag` uses the second diagonal of g, and the third
conclusion uses the second structural diagonal of B. I checked the targets of
each corresponding `t` binder against its `HasSpaceBaseChange` argument.
Every projection is tied to the actual 2-base change. Properness is algebraic-space
properness, avoiding both a DM assumption and the invalid source-local test of
properness on arbitrary etale charts. Finite inertia uses exactly the existing
finite scheme-test predicate. No mathematical mismatch or disputed statement
was found. The only repair during validation was the long-line wrap.
