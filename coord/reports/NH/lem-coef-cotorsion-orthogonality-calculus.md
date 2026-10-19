## Worker report

The module `Sheaf.CategoryTheory.CotorsionOrthogonalityCalculus` states
`CategoryTheory.cotorsion_orthogonality_calculus` with exactly one `sorry`.
Its three accompanying real predicate definitions render notions explicitly introduced
by this node: `CategoryTheory.SplittingOrthogonal`,
`CategoryTheory.ObjectProperty.leftSplittingOrthogonal`, and
`CategoryTheory.ObjectProperty.rightSplittingOrthogonal`. They are helpers of this
node, listed in `lean.declarations`, not statements of other DAG nodes. No independent
new notion or dependency repair is needed. The original node's fields remain unchanged
except for `lean`. The theorem docstring reproduces all ten DAG proof steps.

Hypothesis and clause correspondence:

- An arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  Both object and morphism universes are explicitly bound and independent. There is
  no enough-injectives, enough-projectives, Grothendieck or Ext-smallness assumption.
- `U ⟂₁ V` is `SplittingOrthogonal U V`: for every `E : C`, `k : V ⟶ E`,
  `q : E ⟶ U`, and complex equation `h : k ≫ q = 0`, the hypothesis
  `(ShortComplex.mk k q h).ShortExact` implies
  `∃ s : U ⟶ E, s ≫ q = 𝟙 U`. This is literally a section of the epimorphism,
  not a chosen splitting or an arbitrary Ext object.
- An arbitrary class is `(S : ObjectProperty C)`, Mathlib's abbreviation for `C → Prop`.
  The left predicate is `fun U ↦ ∀ V : C, S V → SplittingOrthogonal U V`;
  the right predicate is `fun V ↦ ∀ U : C, S U → SplittingOrthogonal U V`.
  No closure or nonemptiness assumption is made on S.
- Both classes contain zero: the theorem's first conjunct is
  `S.leftSplittingOrthogonal (0 : C) ∧ S.rightSplittingOrthogonal (0 : C)`.
  This uses the canonical zero-object notation provided by the scoped Mathlib
  `ZeroObject` instance, not a newly postulated zero object.
- Retracts: for every `X Y`, `s : X ⟶ Y`, `r : Y ⟶ X`, and
  `s ≫ r = 𝟙 X`, the second conjunct gives both
  `S.leftSplittingOrthogonal Y → S.leftSplittingOrthogonal X` and
  `S.rightSplittingOrthogonal Y → S.rightSplittingOrthogonal X`.
- Extensions: for every `T : ShortComplex C`, `T.ShortExact`, the third conjunct
  gives `S.leftSplittingOrthogonal T.X₁ → S.leftSplittingOrthogonal T.X₃ →
  S.leftSplittingOrthogonal T.X₂`, and the identical assertion for the right class.
  The endpoints are X and Z, and the conclusion is membership of the middle Y.
- Diagonal fillers: the last conjunct universally quantifies `A B X Y`,
  `i : A ⟶ B`, `p : X ⟶ Y`, and assumes exactly `Mono i`, `Epi p`,
  and `SplittingOrthogonal (cokernel i) (kernel p)`.
  The kernel and cokernel are Mathlib's categorical universal constructions.
- Arbitrary commuting square: for every `a : A ⟶ X` and `b : B ⟶ Y`,
  `a ≫ p = i ≫ b` renders `p a = b i`.
  The conclusion `∃ d : B ⟶ X, i ≫ d = a ∧ d ≫ p = b` renders both required
  triangle equations. Composition is diagrammatic throughout Lean.

Statement dependencies read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Read the full class and docstring:
  preadditive, normal monos/epis, finite products, kernels and cokernels.
- `def-weil-pbc-exact-sequence`: its recorded declarations include
  `CategoryTheory.ShortComplex.ShortExact`; the recorded module
  `Mathlib.Algebra.Homology.ExactSequence` is publicly imported, as is the actual
  declaration's module `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
  Read `ShortExact` in full: exactness, monic first arrow, epic second arrow.
  `ShortComplex.mk` supplies the complex equation. This is the categorical version
  of the dependency's exact-sequence notion, appropriate to an arbitrary category.
- `CategoryTheory.ObjectProperty` from `Mathlib.CategoryTheory.ObjectProperty.Basic`
  is the existing class-of-objects representation.

The stated proof inputs are imported privately as required by the stage rules:

- `lem-weil-pbc-abelian-exact-epi-cokernel`: Mathlib's
  `CategoryTheory.ShortComplex.Exact.gIsCokernel` (available through the public
  exact-sequence import), kernel/cokernel and abelian-category infrastructure.
- `lem-sp-abelian-refinements`: `Mathlib.CategoryTheory.Abelian.Refinements`,
  `CategoryTheory.epi_iff_surjective_up_to_refinements` and
  `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`.
- `lem-weil-pbc-snake-lemma-abelian`:
  `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`,
  `CategoryTheory.ShortComplex.SnakeInput.snake_lemma`.
- `lem-weil-pbc-pushout-short-exact-sequence`:
  `Sheaf.CategoryTheory.PushoutShortExactSequence`,
  `CategoryTheory.pushout_short_exact_sequence`; read the full declaration and docstring.
- `lem-weil-pbc-pushout-kernel-iso`: `Mathlib.CategoryTheory.Abelian.CommSq`,
  `CategoryTheory.Abelian.epi_kernel_map_of_isPushout` and the monic-composite
  argument identified by the dependency record.

Edge cases checked before the statement was written:

- Empty S: both orthogonals are all objects, since membership in S is a hypothesis
  in the defining universal quantifier. Zero, retract and extension clauses remain valid.
- Zero objects in either argument: an extension with zero subobject or zero quotient
  has an isomorphic remaining nonzero arrow and therefore splits; neither case is excluded.
- Identity retracts and arbitrary (possibly nonskeletal) retracts: the exact equation
  `s ≫ r = 𝟙 X` makes sense without choosing a direct-sum decomposition.
- Degenerate short exact sequences with an endpoint zero: `T.ShortExact` still
  quantifies over them; there is no nonzero or proper-extension condition.
- If i or p is an isomorphism, its cokernel or kernel is zero and the filler clause
  includes the ordinary inverse-composition filler. If either object is zero the
  displayed equations still have the right types.
- The lifting orthogonality is oriented as cokernel of i against kernel of p,
  not the reverse. Testing the nonsplit extension of Z/2 by Z/2 shows why no
  unconditional splitting or lifting claim may replace that hypothesis.
- No Ext group or universe shrink is used, so large hom universes are not excluded.

Searches performed (2026-10-16), using the required msearch wrapper:

- LeanFinder query: "In an abelian category splitting extension orthogonals are
  closed under retracts and extensions and give diagonal lifts for monomorphisms
  against epimorphisms". Eight hits, including `ObjectProperty.IsSerreClass`,
  `IsSerreClass.toIsClosedUnderExtensions`, and Serre-class morphism properties.
  Read the Serre-class and extension-closure definitions: these assume stronger
  closure hypotheses and do not give splitting orthogonality or this lifting result.
- Loogle query: `"HasLiftingProperty", "ShortExact"`. Zero hits.
- Mathlib grep query: `cotorsion|[Oo]rthogonal|splittingOrthogonal` in CategoryTheory.
  Twenty-five reported hits concern ordinary Hom orthogonals, triangulated
  orthogonals and orthogonal reflection. Read `ObjectProperty.Orthogonal`:
  its predicates assert vanishing of maps, not splitting of extensions.
- LeanSearch query: "Splitting extension orthogonal classes in an abelian category
  contain zero and are closed under retracts and extensions". Eight hits include
  `IsClosedUnderExtensions.mk`, `Splitting.ofExactOfRetraction`,
  `ShortExact.splittingOfInjective`, and idempotent completeness. Read their full
  signatures and docstrings: these are constructors/ingredients or special cases,
  not the present result for arbitrary objects and arbitrary S.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` for cotorsion,
  orthogonal and splittingOrthogonal found ordinary Hom/triangulated orthogonality,
  derived-category uses and unrelated algebraic orthogonal idempotents, no matching
  splitting predicate or complete theorem.
- `grep -rn` for this blueprint id in the upstream source returned no hit.
- Exact-name `rg` over `dag/lean_names_upstream.json`, project Lean, upstream Lean
  and Mathlib for `SplittingOrthogonal`, `leftSplittingOrthogonal`, and
  `cotorsion_orthogonality_calculus` returned no hit before writing the module.

Sources inspected: the recorded blueprint integral exceptional-adjoint proof and
Stacks `homology.tex`, section `section-extensions`, especially
`definition-extension` and the pullback/pushout conventions immediately following.
The DAG explicitly identifies the full calculus as agent-formulated, rather than
claiming that Stacks states the complete lemma. No source-based correction was needed,
and no STATEMENT-DISPUTED issue remains.

Validation: single-file compilation is performed only through the prescribed
`scompile.py NH lem-coef-cotorsion-orthogonality-calculus` wrapper. The first attempts
identified a private-only ShortExact import and the scoped zero-object notation;
both were repaired without changing the mathematical statement. Final compile and
delivery preflight results are recorded below after the dry run.

Final validation results (2026-10-16): `scompile.py` exited 0 with no errors or
warnings; the sandbox and library-module checks each took 1.1 seconds. The required
`deliver2.py NH lem-coef-cotorsion-orthogonality-calculus --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the intentionally pending
independent second reading. Nothing was pushed. The second reader writes that section
and delivers; the worker has not written a second-reading verdict.


## Second reading by NH

Independent second reading on 2026-10-16, with the sandbox node and Lean file open.
I read the complete natural-language statement, all ten proof steps, both statement
Dependency nodes and the signatures of the recorded proof inputs. I also read the
blueprint integral-exceptional-adjoint proof paragraph 2 and Stacks `homology.tex`,
lines 1259–1380 (Tags 010I/010J, the definition of an extension and its pullback and
pushout operations). The latter assumes only an abelian category for these operations.
Its subsequent discussion of the size of Ext sets imposes no hypothesis here: the
statement quantifies over extensions directly and constructs no Ext set. The node
honestly labels the complete calculus agent-formulated; Stacks supplies conventions,
not a purported exact citation of this complete theorem. No repair note exists for
this item. No natural-language statement correction was necessary.

My initial list of the node's objects, hypotheses and conclusions, and the final
Lean correspondence, is as follows. Every row has verdict **exact**.

| Node item | Final Lean rendering and check |
|---|---|
| An arbitrary abelian category A | `{C : Type u} [Category.{v} C] [Abelian C]`; `u` and `v` are explicitly bound independently. The read `Abelian` class supplies precisely preadditivity, finite products, kernels/cokernels and normal monos/epis, hence zero and finite biproducts. No Grothendieck, enough-injectives, enough-projectives or Ext-smallness instance is required. |
| Objects U,V and the relation U perpendicular-one V | The existing `Cotorsion.ExtOneOrthogonal U V` universally binds `E`, `i : V ⟶ E`, `p : E ⟶ U`, `w : i ≫ p = 0`, and asserts `(ShortComplex.mk i p w).ShortExact → IsSplitEpi p`. I opened this actual definition in `SmallCotorsionModelRecognition.lean`, rather than relying on its name. Its binders require only `[Abelian C]`, even though its module's recognition theorem concerns Grothendieck categories. |
| Splitting means a section of the quotient arrow | I opened `Mathlib.CategoryTheory.EpiMono`: `IsSplitEpi p` is `Nonempty (SplitEpi p)`, and `SplitEpi p` has `section_ : U ⟶ E` and `id : section_ ≫ p = 𝟙 U`. This is precisely existence of the section in the node, with no selected section or uniform choice assumption. |
| An arbitrary class S of objects | `(S : ObjectProperty C)`; the opened Mathlib abbreviation is exactly `C → Prop`. No iso-closure or nonemptiness condition on S appears. |
| The left orthogonal | `S.leftSplittingOrthogonal = fun U ↦ ∀ V : C, S V → Cotorsion.ExtOneOrthogonal U V`. The first variable is the quotient object, as required. |
| The right orthogonal | `S.rightSplittingOrthogonal = fun V ↦ ∀ U : C, S U → Cotorsion.ExtOneOrthogonal U V`. The second variable is the subobject, as required. |
| Zero belongs to both classes | First conjunct `S.leftSplittingOrthogonal (0 : C) ∧ S.rightSplittingOrthogonal (0 : C)`. Scoped `ZeroObject` notation uses the zero object already provided by abelianness. |
| Retracts of members belong to either class | Second conjunct binds every `X Y`, `s : X ⟶ Y`, `r : Y ⟶ X`, with `s ≫ r = 𝟙 X`; its two implications take membership of Y to membership of X. This is r composed with s in the node's functional notation, not the opposite retraction equation. |
| Extensions of members belong to either class | Third conjunct binds every `T : ShortComplex C` and `T.ShortExact`, with endpoint hypotheses `T.X₁` and `T.X₃`, concluding `T.X₂`, independently for each orthogonal. I opened `ShortExact`: its fields are `Exact`, `Mono T.f`, `Epi T.g`. `ShortComplex.exact_iff_image_eq_kernel` identifies its exactness with the node's image/kernel equality. |
| The objects and arrows of the lifting square | Last conjunct binds arbitrary `A B X Y : C`, `i : A ⟶ B`, `p : X ⟶ Y`. It assumes exactly `Mono i` and `Epi p`. |
| The obstruction vanishes | `Cotorsion.ExtOneOrthogonal (cokernel i) (kernel p)`. These are Mathlib's canonical categorical kernel and cokernel; order is cokernel first, kernel second, matching the extension of Coker(i) by Ker(p). |
| Every commuting pair a,b | After those hypotheses, `∀ (a : A ⟶ X) (b : B ⟶ Y), a ≫ p = i ≫ b → ...`. The equation translates exactly to pa = bi. |
| There is a diagonal making both triangles commute | `∃ d : B ⟶ X, i ≫ d = a ∧ d ≫ p = b`; these are precisely di = a and pd = b. Both equations are present, and d may depend on the square. |

Dependency reading: `def-sp-abelian` records the Mathlib `Abelian` class and
`def-weil-pbc-exact-sequence` explicitly records `ShortComplex.ShortExact` among its
usable declarations, with categorical forms retained for arbitrary abelian categories.
I opened both nodes and those declarations, including `ObjectProperty`, and the
image/kernel comparison. The private proof imports cover the listed exact/cokernel,
refinement, snake and pushout inputs. I opened `Exact.gIsCokernel`, the refinement
criteria, `SnakeInput` and `snake_lemma`, `epi_kernel_map_of_isPushout`, and the full
landed `pushout_short_exact_sequence` signature: it supplies the pushed-out sequence,
its projection, uniqueness, and the three vertical components, with independent
object and Hom universes. None requires a dependency repair for this statement.

Edge cases: the empty class makes either orthogonal the full class by its conditional
universal quantifier. Zero as either extension endpoint is included; a zero quotient
has the unique section, and a zero subobject makes the epic quotient an isomorphism.
The zero category and all zero square objects are included. Identity retracts,
isomorphic arrows i or p, and short exact sequences with zero endpoints satisfy the
same binders and are not excluded. General retracts need no chosen complementary
summand. There is no scheme, integer degree or coefficient ring in this node, so the
empty-scheme, n = 0 and characteristic cases impose no further restriction. The
universes u and v need not agree; no Ext object with a fixed universe is introduced.
Every quantifier has the node's dependency order. The unused outer S in the independent
lifting conjunct imposes no restriction, since every category has the empty predicate.

Independent searches, through the prescribed wrapper where applicable:

- LeanFinder: “A short exact extension of U by V admits a section; the class of all U
  with this property for every V in a class is closed under direct summands and
  extensions”. Eight hits, including `ObjectProperty.IsSerreClass` and
  `IsClosedUnderExtensions`. I opened both class signatures: they assume closure
  rather than establish it for splitting orthogonals, and the Serre condition is
  stronger. None is the requested theorem.
- Loogle: `"ShortExact", "section"` returned zero hits.
- LeanSearch: “A monomorphism has the left lifting property against an epimorphism if
  every extension of its cokernel by the kernel of the epimorphism splits”. Eight
  hits included `StrongMono.mk'`, `StrongMono.rlp`, `StrongEpi.llp`, `Abelian.monoLift`,
  `epiIsCokernelOfKernel`, a four-lemma, and `llp_rlp_monomorphisms`. Their signatures
  concern epi-against-mono lifting, an ordinary kernel factorization, or a
  Grothendieck generator; none states this opposite lifting orientation under the
  splitting obstruction or the full calculus.
- Independent `rg` on Mathlib CategoryTheory/Homology, upstream `WeilConjectures`,
  and project `lean/Sheaf`, using
  `cotorsion|extension.?orthogonal|splitting.?orthogonal|ext.?orthogonal`, FOUND
  `CategoryTheory.Cotorsion.ExtOneOrthogonal` in the landed project module
  `Sheaf.CategoryTheory.SmallCotorsionModelRecognition`, reused also by
  `FlatComplexCotorsionPairs`. Upstream hits were Serpe bibliographic references.
  Reading `ObjectProperty.Orthogonal` confirmed that Mathlib's ordinary left/right
  orthogonals test vanishing morphisms, rather than split extensions.
- Exact-name `rg` across `dag/lean_names_upstream.json`, upstream, Mathlib and the
  project found no declaration of either new left/right orthogonal helper or the
  complete calculus theorem. DAG cotorsion searches found the recognition and
  complex-lifting nodes; none already records this calculus as a Lean theorem.
  The full statement is therefore still a new module, rather than `existing: true`.

Mismatch and repair (H4): contrary to the original worker report's no-match claim,
its new `CategoryTheory.SplittingOrthogonal` duplicated the existing
`CategoryTheory.Cotorsion.ExtOneOrthogonal` just inspected. I removed the duplicate
predicate and its docstring, added a public import of its owning landed module,
used the existing predicate in both left/right helpers and the lifting hypothesis,
and updated the module definition list, `lean.declarations` and `lean.statement`.
The worker report above is retained as requested; this section supersedes its
three-definition count and no-matching-predicate assertion. The two remaining
helpers are real lambda definitions of notions explicitly introduced in this node.
No new independent notion, new DAG node, dependency module or natural-language
statement correction is needed. All other correct text and the full ten-step
proof docstring were preserved.

Import-cycle note for landing: the recognition theorem is mathematically downstream
of this calculus, but its already landed predicate is foundational and requires only
Abelian. Reusing that predicate introduces no DAG edge to the recognition theorem
and no current Lean import cycle. Under stages/2-statements.md §3(7), OMIT the future
automatic private proof import of this calculus into
`Sheaf.CategoryTheory.SmallCotorsionModelRecognition`, since it would close the
source import cycle. Moving the shared predicate to a separate foundational module
can be handled as a coordinated later interface refactor; this delivery neither
copies it nor edits the landed recognition module.

Final checks: all three delivered declarations have source/blueprint docstrings;
the two definitions have real data and the sole theorem has exactly `by sorry`.
No variables or universes are auto-implicit (`set_option autoImplicit false`).
The node's `lean.statement` was extracted verbatim from the final theorem signature.
The prescribed `scompile.py` compiled the sandbox file and library module cleanly
(exit 0, 1.3 s and 1.4 s respectively), without warnings. There is one delivered Lean
file and no sibling dependency module to compile.

Delivery dry run: `deliver2.py NH lem-coef-cotorsion-orthogonality-calculus --no-push`
printed `OK (dry run)` at 94333f4df8: compilation and full stage-2 preflight passed.
The final signature equality, 100-character Lean line widths, one theorem sorry,
and unchanged non-Lean node fields were also checked mechanically.
