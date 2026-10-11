## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.PullbackExtensionClass` states
`AlgebraicGeometry.Scheme.Modules.pullback_extClass_precompose`. Its only theorem
has proof `sorry`; it introduces no definitions and changes only the item's `lean` record.

Hypothesis and clause correspondence:

- A scheme X: `{X : Scheme.{u}}`, with explicit universe `u` and `autoImplicit false`.
- O_X-modules A, E, C, the maps i and p, and their short exact sequence:
  `S : ShortComplex X.Modules`, `hS : S.ShortExact`; A = S.X₁, E = S.X₂,
  C = S.X₃, i = S.f, p = S.g. There is no quasi-coherence or finiteness restriction.
- Ext as in def-sc-ext-sheaf: `[HasExt.{u} X.Modules]`, the recorded upstream
  universe/instance convention, and the annotation `Ext C' S.X₁ 1`.
  This is infrastructure for the existing Ext definition, not a new geometric hypothesis.
- The Yoneda class δ is `hS.extClass`, Mathlib's class of this exact sequence;
  no arbitrary class is substituted for it.
- Every O_X-linear morphism C' → C: `{C' : X.Modules} (u : C' ⟶ S.X₃)`.
  It is not required to be mono or epi.
- The pullback middle object: `Limits.pullback S.g u` in the category X.Modules.
  This is a fiber product of modules on X, not pullback along a scheme morphism.
- Its maps: the quotient is `pullback.snd S.g u`; the existential inclusion `j`
  satisfies `hz : j ≫ pullback.snd S.g u = 0` and
  `j ≫ pullback.fst S.g u = S.f`. Together these specify the canonical map
  a ↦ (i(a),0) uniquely by the pullback universal property. Thus j is not
  an unconstrained map or additional input hypothesis. The zero equation is the
  structural proof needed by `ShortComplex.mk`, not a redundant conjunct.
- The pullback is a short exact sequence: the conclusion supplies
  `hp : (ShortComplex.mk j (pullback.snd S.g u) hz).ShortExact`.
  This realizes the short exactness already implicit in the phrase
  "pullback short exact sequence" and required to define its class.
- Its Yoneda class is δ ∘ u: `(hp.extClass : Ext C' S.X₁ 1) =
  (Abelian.Ext.mk₀ u).comp hS.extClass (zero_add 1)`.
  Ext.comp uses diagrammatic order: first the degree-zero u, then δ. The degree
  equality is 0 + 1 = 1, so the target is precisely Ext¹_X(C', A).

Dependencies read and used:

- `WeilConjectures.AlgebraicGeometry.Modules.Ext`, declaration
  `AlgebraicGeometry.Scheme.Modules.Ext` (def-sc-ext-sheaf), the existing
  abbreviation for `Abelian.Ext` on X.Modules. The upstream docstring still
  repeats the old contravariant derived-functor wording; the node's correction
  and its lean_candidates explain that its actual derived-category definition
  is the corrected Ext notion. No dependency repair is needed.
- `Sheaf.AlgebraicGeometry.Modules.ExtYonedaFunctoriality`, declaration
  `AlgebraicGeometry.Scheme.Modules.ext_yoneda_functoriality`
  (lem-sc-p1-ext-yoneda-functoriality), read in full. Its first clause identifies
  the contravariant Ext map with the degree-zero composition in our conclusion;
  the module is imported and the docstring names this final proof step.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass`, declarations
  `CategoryTheory.ShortComplex.ShortExact.extClass` and `extClass_naturality`.
  Naturality supplies the second proof step after constructing (1, fst, u).
  The docstring carries all three original node proof steps.

Edge cases checked mathematically before writing: u = identity recovers the
original extension up to its canonical fiber-product isomorphism; u = zero
produces a split pullback with zero class; C' = zero is included; a split
original extension remains split. Zero A, E or C and the empty scheme cause
no exclusions. No base field, characteristic, nonemptiness, or finite-type
assumption is introduced. The chosen Ext universe is precisely the recorded
scheme-module dependency convention.

Searches (2026-10-11):

- msearch.py leanfinder: "Yoneda class of pullback short exact sequence equals
  precomposition with quotient morphism": 8 hits, all ShortComplex.SnakeInput
  constructions/identities for the snake lemma, none the extension-class formula.
- msearch.py loogle: "CategoryTheory.ShortComplex.ShortExact.extClass, pullback":
  0 hits, unknown identifier 'pullback'. This is recorded as a failed query,
  not evidence by itself that the formula is absent.
- msearch.py grep: "pullback|extClass" in Algebra/Homology/ShortComplex:
  8 hits, concrete pullback and SnakeInput definitions, no formula.
- rg of "pullback|extClass" in project/upstream module directories: found
  upstream Ext and scheme pullback infrastructure, and the project's sibling
  `pushout_extClass_postcompose`; no pulled-back extension-class statement.
- rg of "lem-sc-p1-pullback-extension-class" throughout upstream
  WeilConjectures: no hits.
- rg of "pullback_extClass_precompose|pullback.*extClass|extClass.*pullback"
  throughout Mathlib, WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json:
  no hits; proposed declaration name is unused.

Source verification: this machine lacks the untracked Stacks TeX files. Read
[Stacks 010I](https://stacks.math.columbia.edu/tag/010I), particularly the
construction of the pullback extension and its commutative diagram, and
[Stacks 06XP](https://stacks.math.columbia.edu/tag/06XP), the Ext/Yoneda discussion.
No statement correction or disputed mathematical point was found. No new nodes
or dependency modules were needed because Mathlib already supplies fiber
products, short complexes, short exactness, degree-zero classes, and Ext composition.

Validation: the first server compile found that the unqualified word `pullback`
inside Scheme.Modules resolved to scheme-module pullback; it was corrected to
`Limits.pullback`. Subsequent validation uses the server single-file compiler and
`deliver2.py --no-push`. No local compilation or manual git command was run.

## Second reading by H1

I reread the node statement, its Stacks source places (010I for the pullback
extension construction and 06XP for Ext/Yoneda functoriality), the dependency
nodes, and the Lean module line by line. The correspondence is:

- The scheme (X) is `{X : Scheme.{u}}`; no base field, characteristic,
  finiteness, separation, or nonemptiness hypothesis is added.
- The short exact sequence (0\to A\to E\to C\to0) is
  `(S : ShortComplex X.Modules) (hS : S.ShortExact)`, with `S.X₁`, `S.X₂`,
  `S.X₃`, `S.f`, and `S.g` rendering (A,E,C,i,p).
- The Ext convention is exactly the dependency declaration
  `AlgebraicGeometry.Scheme.Modules.Ext`, supplied by
  `[HasExt.{u} X.Modules]`; the class δ is `hS.extClass`.
- A test module and quotient morphism (u:C'\to C) are
  `{C' : X.Modules} (u : C' ⟶ S.X₃)`, with no mono/epi assumption.
- The pullback middle object is the categorical module pullback
  `Limits.pullback S.g u`; its quotient map and first projection are
  `pullback.snd S.g u` and `pullback.fst S.g u`.
- The existential `j` and equation `j ≫ pullback.snd S.g u = 0`, together with
  `j ≫ pullback.fst S.g u = S.f`, specify the canonical inclusion
  (A\to E\times_C C') (the ((i(a),0)) map), rather than adding an arbitrary
  datum. `hp : (ShortComplex.mk j (pullback.snd S.g u) hz).ShortExact` states
  the pulled-back short exact sequence.
- The final equality has the same quantifier order and target as the node:
  `(hp.extClass : Ext C' S.X₁ 1) =
  (Abelian.Ext.mk₀ u).comp hS.extClass (zero_add 1)`, i.e. the Yoneda class
  δ precomposed by (u), with the degree equality (0+1=1).

No mismatch was found and no Lean or node text was changed. The existential
presentation covers identity and zero (u), zero modules, (C'=0), split
extensions, and empty schemes without extra assumptions; `n=0` is irrelevant
to this degree-one statement. The source and dependency declarations use the
same categorical pullback and Ext objects, so there is no alternate notion or
unbound universe. Searches recorded in the worker report found no existing
pullback/extClass declaration in Mathlib, the upstream source, or `lean/Sheaf`.
The module compiles cleanly with `scompile.py` (only its permitted `sorry`).

Independent searches (2026-10-11): `msearch.py leanfinder` with "base change of
an extension in an abelian category induces the contravariant map on Ext one"
returned eight abstract Ext functor/composition hits, without the pullback
sequence statement. `msearch.py loogle` with
"CategoryTheory.ShortComplex.ShortExact.extClass" returned twelve hits,
including `extClass_naturality` and Ext exactness, but no construction/class
formula for the pullback. `msearch.py grep` with
"extClass.*pullback|pullback.*extClass" returned zero hits. Independent `rg`
searches of upstream `WeilConjectures`, project `lean/Sheaf`, and upstream-name
records found the pushout sibling and the upstream Ext/Map lifting criteria;
opening that upstream module confirmed that its statements concern vanishing
after exact functors, not the class of the categorical pullback sequence.
The dependency signatures and `extClass_naturality` were opened and read.
There are no new nodes, dependency modules, or statement correction to review.

Because the local Stacks TeX is absent, I read the complete sections
`homology.tex` at `section-extensions` and `derived.tex` at `section-ext` from
the Stacks upstream raw source, as well as [010I](https://stacks.math.columbia.edu/tag/010I)
and [06XP](https://stacks.math.columbia.edu/tag/06XP). These require an abelian
category, with no stronger assumptions for the pullback or Yoneda class
formula; `X.Modules` supplies that structure. The docstring carries all three
node proof steps. There are no definitions, private copies, file-local
instances/notations, or actual proofs in this delivery.
