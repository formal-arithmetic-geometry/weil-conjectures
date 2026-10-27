## Worker report

The delivery states `CategoryTheory.ObjectProperty.fp2_ind_realization` in
`lean/Sheaf/CategoryTheory/FP2IndRealization.lean`, with its whole proof `sorry`.
No definitions or other postponed theorems are introduced. The accepted stage-1
split and ten-step proof are preserved. The statement now explicitly identifies
the small Ext1 model under the authorized correction described below.
The former worker's unchanged-item failure concerned the reviewed split; this
stage-2 packet adds the previously absent Lean record and module.

Hypotheses, one by one:

- The indexing/Hom universe of def-weil-size-convention is `w`. The object and
  original morphism universes are independent `u` and `v`; no equality or size
  inequality is imposed on them.
- The locally small Grothendieck abelian ambient category is
  `(B : Type u) [Category.{v} B] [Abelian B]
  [IsGrothendieckAbelian.{w} B]`. Mathlib's latter class supplies
  `LocallySmall.{w} B`, a separator, and exact `w`-small filtered colimits;
  `IsGrothendieckAbelian.hasColimits` supplies all colimits in that universe.
  No redundant `HasColimits` assumption is added.
- The full subcategory is `P : ObjectProperty B`; its full subcategory is
  `P.FullSubcategory`. `[EssentiallySmall.{w} P.FullSubcategory]` expresses its
  small skeleton and `[P.IsClosedUnderIsomorphisms]` its repleteness.
- Containment of zero is `[P.ContainsZero]`. This means a zero object belongs;
  repleteness makes it equivalent to containing every ambient zero object.
- The three ambient closure assumptions are `[P.IsClosedUnderKernels]`,
  `[P.IsClosedUnderCokernels]`, `[P.IsClosedUnderExtensions]`. These are weak
  Serre closure, not the stronger closure under every ambient subobject/quotient.
- The bijective Hom comparison for every member of P and every small filtered
  ambient diagram is `hHom : P ≤ isFinitelyPresentable.{w} B`. The exact equivalence
  is Mathlib `isFinitelyPresentable_iff_preservesFilteredColimitsOfSize` in
  CategoryTheory/Presentable/Finite.lean, lines 67--69.
- Yoneda Ext-one comparison bijectivity is
  `hExt : ∀ C : B, P C → PreservesFilteredColimitsOfSize.{w, w}
  (Abelian.extFunctorObj.{w} C 1)`. This is the usual small model of the SAME
  Yoneda group, justified by the existing proved comparison below. The functor
  has value `Abelian.Ext.{w} C N 1` and acts by postcomposition with `Ext.mk₀ f`.
  Preservation is equivalent to the canonical comparison being an isomorphism.
  For abelian groups this is equivalent to the underlying map being bijective;
  filtered colimits are created by the forgetful functor to sets. Hence this
  includes both surjectivity and injectivity for arbitrary ambient diagrams.

The Yoneda model is not replaced by an arbitrary Ext theory or an added
comparison assumption. The already proved
`CategoryTheory.nonempty_yonedaDerivedExtComparison B` yields a natural additive
bijection from `YonedaExtension.Classes N C 1`, the quotient of actual ambient
short exact sequences fixing endpoints, to the displayed small Ext group.
`shortExact_class` normalizes it as minus the connecting class (conjugated by
endpoint identifications); `naturality` identifies maps in N with pushout;
`baer_sum` identifies the group law with the actual geometric Baer sum. The
uniform minus sign commutes with every coefficient map and therefore with the
canonical colimit comparison. `HasExt.{w} B` follows from Grothendieckness by
Mathlib's `IsGrothendieckAbelian.hasExt`, not a further hypothesis. Transport
along this proved natural Baer isomorphism gives exactly the node's canonical
Yoneda Ext comparison. No derived-versus-Yoneda theorem is assumed of the user.
The comparison theorem only justifies this interpretation; it is not a statement
dependency and its module is not imported. The actual small Ext carrier and
functor come from the definition node `def-pc-ext`, now explicitly cited in the
corrected statement and in stmt_deps. No extension data are redeclared.

Conclusions, clause by clause:

- J is `ind.{w} P`, Mathlib's actual property of admitting a `w`-small filtered
  colimit presentation with every stage in P. Its definition quantifies over
  arbitrary functors, not just monomorphism diagrams. Its built-in closure under
  isomorphisms gives the full replete hull.
- J contains zero: `(ind.{w} P).ContainsZero`.
- J contains C: `P ≤ ind.{w} P`.
- Closure under all small filtered ambient colimits:
  `∀ (I : Type w) [SmallCategory I] [IsFiltered I],
  (ind.{w} P).IsClosedUnderColimitsOfShape I`.
- Closure under every small ambient coproduct:
  `∀ I : Type w, (ind.{w} P).IsClosedUnderColimitsOfShape (Discrete I)`.
- Closure under ambient kernels and cokernels:
  `(ind.{w} P).IsClosedUnderKernels ∧ (ind.{w} P).IsClosedUnderCokernels`.
- Closure under every ambient short exact extension:
  `(ind.{w} P).IsClosedUnderExtensions`. Its definition quantifies over every
  `S : ShortComplex B` with `S.ShortExact`, and requires only membership of
  `S.X₁` and `S.X₃`; there is no finite-stage lift or chosen presentation assumption.
- All resulting presentations use the same universe because every concluding
  predicate is on `ind.{w} P`, and both shape quantifiers also use `w`.

Dependency declarations read and used:

- `def-weil-size-convention`: the recorded metatheoretic convention has no
  declaration; explicit `universe w v u` supplies the size parameters.
- `def-sp-grothendieck-abelian`: Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian`, including its locally-small, AB5 and
  small-colimit instances; the HasExt module imports it publicly.
- `def-weil-pbc-category-colimit`: Mathlib.CategoryTheory.Limits.HasLimits,
  `CategoryTheory.Limits.Cocone`, `IsColimit`, `colimit`, `colimit.desc`, and
  `CategoryTheory.IsFiltered`, used through ind and closure-of-colimits predicates.
- `def-pc-ext`: Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic,
  `CategoryTheory.Abelian.Ext` and `CategoryTheory.Abelian.extFunctorObj`.
  Both are public imports and are used in the Ext continuity hypothesis.
- Interpretation only (not a statement dependency or import):
  Sheaf.CategoryTheory.YonedaDerivedExtComparison,
  `CategoryTheory.YonedaDerivedExtComparison` and
  `CategoryTheory.nonempty_yonedaDerivedExtComparison`. Read the full structure,
  its source/proof docstrings, and the proved theorem. Also read the public
  YonedaExtensionData module's sequence, endpoint-fixed relation, Classes and BaerSum.
- Proof imports: `lem-sfb-ind-fp-idempotence` is
  Mathlib.CategoryTheory.ObjectProperty.Ind, `ObjectProperty.ind_ind`;
  `lem-sfb-arrow-exact-colimits` is Sheaf.CategoryTheory.ArrowExactColimits,
  `CategoryTheory.Limits.arrow_exact_colimits`;
  `lem-weil-pbc-filtered-colimit-sets-elementwise` is Mathlib's
  `Types.jointly_surjective`, `Types.FilteredColimit.isColimit_eq_iff` and
  `isColimit_eq_iff'` (Types.Filtered publicly imports Types.Colimits);
  `lem-weil-pbc-initial-functor-cofiltered-criterion` is Mathlib's
  `Functor.initial_of_exists_of_isCofiltered`, `IsCofiltered.over`,
  `IsCofiltered.of_initial`, `Functor.final_op_of_initial`, and
  `Functor.Final.colimitIso` with the existence equivalence
  (Filtered.Final publicly imports Limits.Final);
  `lem-weil-pbc-pushout-short-exact-sequence` is
  WeilConjectures.CategoryTheory.PushoutShortExactSequence,
  `CategoryTheory.pushout_short_exact_sequence`.
  `def-sp-abelian` is Mathlib `CategoryTheory.Abelian`.

Edge cases checked: P={zero}, including a zero ambient category; empty coproducts
(the Discrete Empty shape); singleton constant presentations (containment);
nonempty filteredness (Mathlib IsFiltered, not IsFilteredOrEmpty); nonmonic
transition maps; arbitrary maps for kernel/cokernel closure; arbitrary ambient
extensions, with no chosen lifts; independent ambient object/morphism universes;
and a skeleton small in precisely the universe used by the hull. No false or
ill-typed clause was found. The source-based correction below makes the equivalent
small Ext1 rendering and its definition dependency explicit.

Searches actually run:

1. `msearch.py ... leanfinder` query: “The filtered colimit closure of an essentially
   small weak Serre subcategory whose Hom and Yoneda Ext1 commute with filtered
   colimits is closed under kernels cokernels extensions and coproducts”. Eight
   hits, including `ObjectProperty.IsSerreClass` and Grothendieck category facts;
   none states this hull-closure result. SerreClass is stronger than weak Serre.
2. `msearch.py ... loogle` query:
   `CategoryTheory.ObjectProperty.ind, CategoryTheory.Abelian.Ext`: zero hits.
3. `msearch.py ... grep` query `Ext.*[Ff]unctor|IsClosedUnderExtensions.*ind`
   in CategoryTheory: 25 returned lines, generic Ext/functor occurrences;
   no existing closure theorem.
4. `rg` of Mathlib ObjectProperty/Ind, Extensions, Kernels and Presentable/Finite
   identified and reused ind, the existing closure predicates and finite
   presentability. GrothendieckCategory/HasExt and derived-category Ext/Basic
   provide the small Ext carrier and functor.
5. `rg` of both project roots for `fp2|FP2|ind_realization|indRealization|Yoneda.*[Ee]xt`
   identified the geometric IndHeartRealization, IntegralIndConstructibleHeartClosure
   and existing YonedaExtensionData/DerivedExtComparison. The geometric closure
   theorem has specific integral coefficient/scheme hypotheses and omits this
   general abstract hypothesis/conclusion package. The realization theorem only
   concerns full faithfulness/essential image. Neither is an exact match.
6. `grep -rn 'lem-sfb-fp2-ind-realization' lean/WeilConjectures` found no declaration;
   the corresponding `rg` of dag/lean_names_upstream.json found none. The Sheaf
   parent module mentions this item only in its proof plan, not as a declaration.

Validation: prescribed `scompile.py NB lem-sfb-fp2-ind-realization <module>` passed
both sandbox and actual library-module modes (2.3 s and 4.6 s), with no errors or
unexpected warnings. The dry run and final delivery are recorded below when run.

## Second reading by NB

I reopened the node and module for a separate reading after compilation. This is
a second pass by this worker, not a claim that a separate agent reviewed it; the
dispatcher expressly prohibits spawning agents and the maintainer independently
reviews the delivery. I checked each hypothesis and each conclusion against the
mapping above. The critical checks were weak Serre rather than Serre closure,
actual ind presentations with unrestricted transitions, both directions of the
Hom/Ext comparison, and absence of any finite-stage-lift premise for extensions.
The existing proved natural Baer comparison justifies the standard small Ext
model; its negative connecting-class convention causes no change to continuity.
The theorem uses no independent size bound or hidden implicit variable. Every
proof dependency already having a module is imported with the required visibility;
statement dependencies are public. On repair, I also checked the corrected Ext1
model citation and both consumer uses; the signature and conclusions need no edit.

Historical pre-return dry run: commit `33134918d32` passed the mechanical checks.
The repaired-packet validation is recorded below.

## Statement corrected

Repair of L H2, returned immutable head `685a06f82771`: the saved packet added
`lem-coef-yoneda-derived-ext-comparison` to stmt_deps although no declaration
from that module occurs in the signature. Removed that dependency and its public
import. The comparison remains explanatory in the docstrings and lean.note.
The actual signature uses `def-pc-ext` through `Abelian.extFunctorObj C 1`.
Following the requested §1(C) repair, the node now explicitly renders Yoneda
Ext1 by that small model, via the canonical natural Baer comparison. This records
the definition the Lean uses and preserves the original mathematical condition.

Old statement (verbatim):

Fix the universes of [def-weil-size-convention]. Let $\mathcal B$ be a locally small Grothendieck abelian category [def-sp-grothendieck-abelian] with all small colimits in the indexing universe. Let $\mathcal C\subset\mathcal B$ be an essentially small full replete subcategory containing zero and closed under ambient kernels, cokernels, and extensions. Suppose that for every $C\in\mathcal C$ and every small filtered diagram $(B_i)$ in $\mathcal B$ [def-weil-pbc-category-colimit], the natural maps $\varinjlim_i\operatorname{Hom}(C,B_i)\to\operatorname{Hom}(C,\varinjlim_i B_i)$ and $\varinjlim_i\operatorname{Ext}^1_{\mathrm{Yon}}(C,B_i)\to\operatorname{Ext}^1_{\mathrm{Yon}}(C,\varinjlim_i B_i)$ are bijective. Yoneda $\operatorname{Ext}^1(C,B)$ means equivalence classes of ambient short exact sequences $0\to B\to M\to C\to0$, with Baer sum. Let $\mathcal J$ be the full replete class of small filtered colimits in $\mathcal B$ of objects of $\mathcal C$, with arbitrary morphisms in the diagrams. Then $\mathcal J$ contains zero and $\mathcal C$, is closed under all small filtered ambient colimits and all small ambient coproducts, and is closed under ambient kernels, cokernels and extensions. In the extension assertion every ambient short exact sequence is included, without any assumed lift to finite stages. All resulting presentations use small indexing categories in the same universe.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-ind-heart/sk-prop-ind-heart.proof.md`, Extensions paragraph. It uses
the Ext1 continuity isomorphism to descend actual short exact extensions and
recovers them by pushout. The natural Baer comparison intertwines those pushouts
with the covariant maps of `def-pc-ext`, so the correction retains that argument,
including arbitrary ambient diagrams and extensions. No proof step or proof_deps
changes. The base stmt_deps are preserved in statement_change.old_stmt_deps.

Citer audit: ran `rg -l '"lem-sfb-fp2-ind-realization"' dag/nodes`, then
parsed stmt_deps and proof_deps and read each matching consumer and its proof.
The item itself and `lem-sfb-ind-fp-idempotence` are textual matches only.
The exact two dependency citers are:

- `lem-sfb-finite-complex-heart-filtered-approximation`: holds true. Its scalar-heart Hom and Yoneda Ext1 continuity hypotheses give the same abstract hull-closure conclusion via the canonical natural Baer comparison; no hypothesis, conclusion, or indexing universe changes.
- `lem-sfb-qcqs-finite-complex-heart-filtered-closure`: holds true. Its scalar-heart Hom and Yoneda Ext1 continuity hypotheses give the same abstract hull-closure conclusion via the canonical natural Baer comparison; no hypothesis, conclusion, or indexing universe changes.

Both applications use the scalar-heart FP2 theorem for arbitrary ambient module
diagrams, so transport through the natural comparison supplies exactly hExt.
Neither consumer is edited. The signature remains verbatim, all universes remain
explicit, and the only postponed proof remains fp2_ind_realization.

Initial saved-packet dry run passed at `7eadb8b49b3`; that mechanical success
did not resolve the independent H2 return. This packet repairs H2 substantively.

Repair validation: `scompile.py NB lem-sfb-fp2-ind-realization <module>` passed
in sandbox mode (1.6 s) and actual library-module mode (1.2 s), with no errors
or unexpected warnings. The repaired packet dry run printed
`OK (dry run): commit b1b2fe5704b passes the preflight and compiles; nothing pushed`.
Self-check verified the verbatim Lean signature, exact statement citations and
stmt_deps, verbatim base old_statement/old_stmt_deps, both citers, 100-character
Lean line width, and that only lean, statement, stmt_deps and statement_change
differ from current main. The statement_change has no old_proof or old_proof_deps
because both are unchanged.
