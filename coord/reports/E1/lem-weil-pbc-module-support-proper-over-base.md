## Worker report

The module states `AlgebraicGeometry.Scheme.Modules.module_support_proper_over_base`.
For `f : X ⟶ S` with `[LocallyOfFiniteType f]` and a quasi-coherent finite-type
module `F`, its first conjunct renders closedness of the support as an existential
closed set `Z` whose carrier is `{x | ¬ Subsingleton (F.presheaf.stalk x)}`.
The second conjunct renders proper support as `HasSupportProperOver f F` and
characterizes it by a scheme `Z`, a closed immersion `i : Z ⟶ X`, properness of
`i ≫ f`, sectionwise annihilation
`a ∈ i.ker.idealOfOpens V → a • s = 0`, and the equivalent finite-type,
quasi-coherent pushforward presentation `F ≅ (pushforward i).obj G`.
Every theorem proof is `sorry`.

The support predicate is `AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`
from `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`. Closed immersions and
proper morphisms use Mathlib declarations `IsClosedImmersion` and `IsProper`.
The ideal action uses Mathlib's `Scheme.Hom.ker` and its `idealOfOpens`; module
sections use the Mathlib `Γ` notation and `Scheme.Modules.pushforward`. The
recorded module-pullback declaration is available through the imported
`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated` dependency.
The coherent-module dependency is imported through `Sheaf.AlgebraicGeometry.Coherent`;
its Mathlib predicates `IsQuasicoherent` and `IsFiniteType` render the two module
hypotheses exactly.

Edge cases checked: the support existential permits the empty closed set and the
zero module; no nonemptiness of `X`, `S`, or `Z` is imposed. The universe is shared
(`Scheme.{u}` throughout), and no characteristic or finiteness assumption beyond
`LocallyOfFiniteType f` and finite type of `F` is added.

Searches for an existing statement/definition: `msearch.py E1
lem-weil-pbc-module-support-proper-over-base leanfinder "support of a finite type
quasi-coherent module on a scheme is closed and proper over a base iff annihilated
by a proper closed subscheme"` found no project declaration; `msearch.py ...
loogle "HasSupportProperOver module_support_proper_over_base"` found no match;
`msearch.py ... grep "support.*proper|annihilator" Mathlib/AlgebraicGeometry`
found only ideal-sheaf/ring-level support results. `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no statement with this theorem's
characterization. The existing `HasSupportProperOver` definition was reused.

## Earlier second reading (a previous round; superseded)

The theorem was reread against the node clause by clause. The first conjunct is
exactly closedness of the nonzero-stalk support. The second conjunct retains the
proper-over-base predicate and introduces exactly a closed subscheme, its closed
immersion, proper composite, ideal annihilation on every open and section, and the
finite-type quasi-coherent pushforward reformulation. No hypotheses or edge cases
were added beyond the node's locally finite type morphism and finite type
quasi-coherent module assumptions.

## Second reading by E1

I independently opened the item JSON and the Lean module, and read Stacks
coherent.tex, the paragraph before lemma-module-support-proper-over-base and
that lemma and proof (0CYS); morphisms.tex, lemma-support-finite-type (056J),
lemma-scheme-theoretic-support (05JU), and definition-scheme-theoretic-support
(05JV). The local literature directory lacks these tex files; the available
copies read were /home/ubuntu/c1-stacks-review/coherent.tex and morphisms.tex.
The source has precisely locally finite type f and finite type quasi-coherent F;
there is no standing Noetherian, separated, field, or characteristic assumption.

Clause-by-clause checklist of the node, with the final Lean rendering:

1. Objects X and S are arbitrary schemes: `{X S : Scheme.{u}}`. The named
   morphism is `(f : X ⟶ S)`. Verdict: exact, with arbitrary universe u.
2. f locally of finite type: `[LocallyOfFiniteType f]`, the declaration of
   def-weil-finite-type-morphism in Mathlib.Morphisms.FiniteType. I read its
   finiteType_appLE field; it imposes finite type on affine ring maps, not
   quasi-compactness of f. Verdict: exact.
3. F an O_X-module: `(F : X.Modules)`, Mathlib's SheafOfModules on X.ringCatSheaf.
   Quasi-coherence and finite type are `[F.IsQuasicoherent] [F.IsFiniteType]`.
   I opened pqf-def-coherent and Coherent.lean and read the Mathlib classes
   IsQuasicoherent (locally a cokernel of free module maps) and IsFiniteType
   (finite local generators). Neither coherence nor Noetherianity is assumed.
   Verdict: exact.
4. Support is the nonzero-stalk locus: `{x : X | ¬ Subsingleton
   (F.presheaf.stalk x)}`. Closedness is the first existential Closeds witness
   with carrier equal to this set. I opened def-weil-pbc-closed-subset-proper-over-base
   and ClosedSubsetProperOverBase.lean: HasSupportProperOver uses exactly this
   locus and properness of its reduced induced closed subscheme. Verdict: exact.
5. Proper support iff there is a proper closed subscheme annihilating F:
   `HasSupportProperOver f F ↔ ∃ (Z : Scheme.{u}) (i : Z ⟶ X)
   (_ : IsClosedImmersion i), IsProper (i ≫ f) ∧ ...`.
   I read the dependency nodes and Mathlib class signatures IsClosedImmersion
   (closed embedding and surjectivity on stalks) and IsProper (separated,
   universally closed, locally finite type; universally closed supplies
   quasi-compactness). Verdict: exact; no properness of X is assumed.
6. Quasi-coherent defining ideal sheaf: `i.ker`, the recorded declaration of
   def-sbc-closed-immersion-ideal-sheaf. I read Hom.ker and ker_apply: it is
   IdealSheafData, with affine component equal to the kernel for quasi-compact
   morphisms, including closed immersions. Thus quasi-coherence is part of the
   encoding, not a missing hypothesis. Verdict: exact.
7. Ideal annihilation on every common open: `∀ (V : X.Opens) (a : Γ(X, V)),
   a ∈ i.ker.idealOfOpens V → ∀ s : Γ(F, V), a • s = 0`.
   I read IdealSheaf.Module.idealOfOpens and idealOfOpens_eq_ideal: these are
   genuine ideal sections on arbitrary opens, not just affine opens. Verdict: exact.
8. Equivalent finite type quasi-coherent pushforward presentation:
   `∃ (G : Z.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
   Nonempty (F ≅ (pushforward i).obj G)` for the same i.
   Both annihilation and the presentation are recorded for the witness, as the
   source's 01QY equivalence permits. I read Mathlib.Modules.pushforward and
   the imported closedImmersion_pushforward_annihilated signature/docstring:
   it uses tensorPullback, exactly the recorded def-pc-module-pullback, not
   the different Mathlib pullback. I also opened TensorPullback.lean.
   Verdict: the original rendering is retained and agrees with the node.
9. One may choose the scheme-theoretic support, whose ideal is Ann(F) and
   underlying set is Supp(F): THIS WAS ABSENT from the original signature.
   Added the final conjunct with a closed immersion i, `∀ U : X.affineOpens,
   i.ker.ideal U = Module.annihilator Γ(X, U) Γ(F, U)`, and
   `Set.range i = {x : X | ¬ Subsingleton (F.presheaf.stalk x)}`.
   These determine the annihilator ideal sheaf on the affine basis, hence
   precisely the scheme-theoretic support of 05JU/05JV. The same witness
   has sectionwise annihilation, a finite type quasi-coherent pushforward
   presentation, and `HasSupportProperOver f F ↔ IsProper (i ≫ f)`.
   Verdict after repair: covers the last sentence and source condition (2),
   including the permitted choice of this witness when support is proper.

Edge cases: zero F has empty support and unit annihilator; the final witness
may be the empty closed subscheme. Empty X, S, or Z are not excluded. No
nonempty index set occurs. No integer n or degree is introduced, so n = 0
is not restricted. Schemes need no field or characteristic assumption, and
u is arbitrary throughout. Larger carriers can be lifted into a common
universe; no bound on a test-algebra or test-scheme universe is imposed.

Independent searches used different terms from the worker's queries:
- leanfinder: "finite quasi-coherent sheaf annihilator defines closed subscheme
  with proper support". Eight hits, all IdealSheafData support and constructors;
  these concern the zero locus of an ideal, not this theorem for arbitrary F.
- loogle: `"annihilator"`. Ring/linear algebra and Lean compiler hits only;
  no scheme-module theorem matching the statement.
- leansearch: "A finite type quasi-coherent sheaf has proper scheme theoretic
  support iff it is pushforward from a proper closed subscheme". Service
  unavailable (Internal Server Error); no absence verdict inferred from this.
- rg on Mathlib/AlgebraicGeometry, WeilConjectures, and repository lean/Sheaf
  for `annihilator`, `scheme.theoretic.support`, `support.*proper`,
  `proper.*support`, `schemeTheoreticSupport`, and the proposed declaration.
  Ring-level annihilator results, Hilbert constructions, proper-support descent
  and the existing support predicate occur; no equivalent existing theorem.
  The DAG already carries lem-weil-pbc-scheme-theoretic-support; I read its
  statement. Its annihilator characterization is used inline with existing
  Mathlib ideals, not introduced as a second definition.

Changes: restored the missing scheme-theoretic-support clause, expanded the
proof docstring into the node's five steps with their dependency identifiers,
and synchronized lean.statement verbatim (whitespace-normalized) with the
signature. The existing main closedness and proper-subsheme characterization
were retained. No new definition nodes or dependency modules were needed;
no node statement was changed, so statement_change and citer revalidation
are not applicable. There are no definitions, local notation, private copies,
extra instances, or proofs added. The only theorem proof remains `sorry`.
All variables and universes are explicitly bound; maximum line width is 85.

Validation: scompile.py E1 lem-weil-pbc-module-support-proper-over-base with
the absolute sandbox module path compiled successfully in 3.9 seconds,
with no errors or warnings. The first relative-path compile invocation could
not find the sandbox file; rerunning with the absolute path resolved it.
