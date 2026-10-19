## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteClosedFpApproximation` states
`AlgebraicGeometry.exists_finite_closed_fp_approximation` with a `sorry` proof.
No definitions or proofs were added. The statement agrees with Stacks Project,
Limits, Tag 09YY (`lemma-finite-in-finite-and-finite-presentation`), whose statement
and proof were read in `literature/stacks-project/limits.tex`.

Hypothesis and clause correspondence:

- Schemes `T` and `S`: `{T S : Scheme.{u}}`.
- The base is quasi-compact: `[CompactSpace S]`.
- The base is quasi-separated: `[QuasiSeparatedSpace S]`.
- The given finite morphism: `(p : T ⟶ S) [IsFinite p]`.
- A nonempty directed set: existential `I : Type u`, `Preorder I`,
  `IsDirected I (· ≤ ·)`, and `Nonempty I`. The index universe agrees with the
  scheme universe, following the project convention for inverse limits.
- Schemes and compatible transition maps: `D : Iᵒᵖ ⥤ Scheme.{u}`.
  Functor laws express identity and composition compatibility.
- The structure maps to `S` and their compatibility with transitions:
  `q : D ⟶ (Functor.const Iᵒᵖ).obj S`.
- Compatible projections from `T`: `π : (Functor.const Iᵒᵖ).obj T ⟶ D`.
- Every structure map is finite and of finite presentation:
  `∀ i, IsFinite (q.app i) ∧ LocallyOfFinitePresentation (q.app i) ∧
  QuasiCompact (q.app i) ∧ QuasiSeparated (q.app i)`.
  All three finite-presentation conditions are explicit, as requested by the node.
- Every transition is a closed immersion:
  `∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsClosedImmersion (D.map f)`.
  An arrow in `Iᵒᵖ` goes from the larger index to the smaller one.
- The specified scheme with these projections is the inverse limit in schemes:
  `Nonempty (IsLimit (Cone.mk T π))`.
- Each projection is over `S`: `∀ i, π.app i ≫ q.app i = p`.

Dependency declarations, read with their docstrings and full signatures:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  integral morphisms in its companion `Morphisms.Integral` use
  `AlgebraicGeometry.IsIntegralHom` (def-weil-finite-integral-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`
  (def-sbc-locally-finite-presentation, a Mathlib leaf without a Lean record).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` and `Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiSeparated` and `AlgebraicGeometry.QuasiCompact`.
  The convention dependency def-weil-pbc-scheme-conventions defines nothing new;
  it prescribes these standard properties and the finite-presentation conjunction.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`, read in full and imported;
  its `Cone`/`IsLimit` encoding is used here. Its theorem supplies an arbitrary
  limit cone, while this theorem specifies the given `T` as the cone point.

The proof dependency nodes and their records were inspected. Mathlib proof leaves
are available through the imports of finite morphisms and quasi-separatedness.
The two non-Mathlib proof dependencies lem-weil-pbc-eventually-finite and
lem-weil-pbc-lft-limit-closed-fp have no Lean records yet, so there are no modules
to import for them. Their roles, and all three proof steps of the node, appear
in the theorem docstring.

Edge cases checked: the empty scheme is allowed for either `T` or `S`; no
nonemptiness of a scheme is assumed. A finite finitely presented morphism can
use a singleton system. The index itself is nonempty, so the limit condition
cannot be reduced to an empty-diagram terminal-object claim. A preorder is
allowed, without imposing antisymmetry or countability. No Noetherian,
separatedness, or field hypothesis was added. No condition that projections
be closed immersions was added, since this node does not assert it.

Searches for an existing statement:

- `msearch.py leanfinder`: "A finite scheme over a quasi compact quasi separated
  base is an inverse limit of finite finitely presented schemes with closed
  immersion transition maps". Eight results concern affine-transition limits,
  eventual affineness, finite morphisms, or finite-type morphism descent; none
  gives this approximation theorem.
- `msearch.py loogle`: `"IsFinite", "IsLimit"`. Zero hits.
- `msearch.py grep` in AlgebraicGeometry:
  `finitePresentationApproximation|finite.*finite.*presentation|exists.*finite.*[Ll]imit`.
  Ten hits concern affine space, the definition of local finite presentation,
  and module finite presentation, not the statement.
- `msearch.py leansearch`: "finite morphism inverse limit finite finitely presented
  schemes closed immersion transitions". Service unavailable (Internal Server
  Error); the other searches were used.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `finiteClosed|finite_closed|finite.*approximation|finite.*[Ff]initePresentation`,
  and for the exact proposed declaration name; the latter has no match.
  Searching the item id in upstream also has no match.
- Read the related upstream declarations in
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` and
  `WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation`.
  `Scheme.Hom.nonempty_finitePresentationApproximation` gives finitely presented
  closed models without finite stages; `Scheme.Hom.nonempty_closedFPEmbedding`
  gives only one embedding; `Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`
  gives a cofiltered category without the required closed transitions.
  None is exactly this node's statement. The upstream name index was checked
  for finite-presentation/approximation entries as well.

Validation: `scompile.py NG lem-weil-pbc-finite-closed-fp-approximation` compiled
this file on the server cleanly (1.4 seconds, nice 19, two threads, 60-second
limit). No statement correction, new notion, or dependency replacement was needed.

## Second reading by NG

Read the sandbox node and Lean side by side, and read Limits,
`lemma-finite-in-finite-and-finite-presentation` (Tag 09YY), including its
proof and neighbouring finite closed embedding lemma. The source assumes
only a finite morphism and a quasi-compact quasi-separated base; there is
no standing field, Noetherian, characteristic, or separated-base assumption.
The following is the complete object/hypothesis/conclusion checklist.

- Objects: schemes S and T are `{T S : Scheme.{u}}`; the morphism p is
  `(p : T ⟶ S)`. Verdict: exact. Mathlib Scheme is a locally ringed space
  locally isomorphic to spectra, and its morphisms are scheme morphisms.
- Hypothesis: S quasi-compact is `[CompactSpace S]`; quasi-separated is
  `[QuasiSeparatedSpace S]`. Verdict: exact, without separation or Noetherianness.
- Hypothesis: p finite is `[IsFinite p]`. Verdict: exact. Opened Finite.lean:
  this extends `IsAffineHom p` and requires finite ring maps on affine opens,
  exactly def-weil-finite-integral-morphism, not merely finite type.
- Existential index: nonempty directed I is `∃ (I : Type u) (_ : Preorder I)
  (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)`. Verdict: exact directed-system
  encoding; antisymmetry is unnecessary and equivalent after quotienting.
  The index lives in the schemes' universe, as the project requires.
- Stages T_i and transitions r_ji are `D : Iᵒᵖ ⥤ Scheme.{u}`. Verdict:
  exact; arrows in the opposite preorder run from j to i for j ≥ i, and
  functor laws impose all composition and identity requirements.
- Structure maps p_i are `q : D ⟶ (Functor.const Iᵒᵖ).obj S`. Verdict:
  exact; naturality says transitions are over S.
- Compatible projections are `π : (Functor.const Iᵒᵖ).obj T ⟶ D`.
  Verdict: exact; naturality is the required projection compatibility.
- Each p_i finite and finitely presented is the universally quantified
  conjunction `IsFinite (q.app i) ∧ LocallyOfFinitePresentation (q.app i) ∧
  QuasiCompact (q.app i) ∧ QuasiSeparated (q.app i)`. Verdict: exact,
  including all three finite-presentation conditions in the convention node.
- Each transition closed is `∀ (i j : Iᵒᵖ) (f : i ⟶ j),
  IsClosedImmersion (D.map f)`. Verdict: exact, with no unwarranted
  finite-presentation condition on these closed immersions.
- T with the specified projections is the scheme limit is
  `Nonempty (IsLimit (Cone.mk T π))`. Verdict: exact universal property
  in Scheme, not an unrelated isomorphism or an assumed limit object.
- The projections are S-morphisms is `∀ i : Iᵒᵖ, π.app i ≫ q.app i = p`.
  Verdict: exact. This also fixes the order and compatibility of all
  existentially chosen data with the original p.

Dependency audit: opened all six statement-dependency nodes and their
recorded signatures. Read Scheme.lean and the defining classes in Finite,
Integral, FinitePresentation, ClosedImmersion, QuasiCompact and QuasiSeparated.
Local finite presentation uses finite-presentation ring maps on affine pairs;
closed immersion uses closed embedding plus surjective stalk maps; quasi-separated
morphism uses its quasi-compact diagonal. These are the dependency notions.
The convention node declares no separate notion. Read the full signature and
docstring of `AlgebraicGeometry.exists_limit_affine_transition`: its directed
preorder, opposite diagram, Cone and IsLimit agree with this statement's encoding.
Its additional conclusions do not need repeating here. No dependency replacement
or new definition node is needed. The two unstated non-Mathlib proof dependencies
remain unavailable as source modules; the proof plan correctly names them rather
than supplying substitute declarations. The other proof dependencies are Mathlib
leaves covered by the imports. No delivered sibling/dependency module exists.

Edge cases: empty T and empty S are included; no point or nonempty-scheme
hypothesis occurs. A singleton index handles finite-presentation p, including
empty schemes. An empty index is correctly excluded by the node's explicit
nonempty requirement. There is no dimension, characteristic, positive integer,
field or reducedness assumption. All universe variables and binders are explicit;
u is arbitrary, and I and Scheme use the same u. The existential Preorder
instance supplies the category used by all subsequent binders.

Independent searches used wording different from the worker's:
`msearch.py leanfinder "A finite morphism is a limit of finite finitely presented
schemes along closed embeddings"` returned eight hits (finite limits, IsFinite,
closed immersions being finite, and finite-type descent), none this theorem.
`msearch.py loogle '"IsClosedImmersion", "IsLimit"'` returned zero hits.
The earlier unquoted query was rejected as an unknown identifier and was retried
with quoted names. LeanSearch for "finite morphism as inverse limit of finite
presentation schemes closed immersions" was unavailable (Internal Server Error).
Used rg on Mathlib AlgebraicGeometry/AffineTransitionLimit and on both upstream
WeilConjectures and project lean/Sheaf for `finitePresentationApproximation`,
`FinitePresentationApproximation`, `finite_closed`, `finiteClosed`, `09YY` and
the Stacks lemma label. No exact statement exists. Opened the upstream
`Scheme.Hom.FinitePresentationApproximation` structure and existence theorem:
they have closed transitions but do not require finite stages. Also opened
`Scheme.Hom.nonempty_closedFPEmbedding` (one stage only) and
`Scheme.Hom.exists_finiteApproximation_of_isIntegralHom` (finite finitely
presented stages but no closed-transition condition). None replaces this node.

No mathematical or convention mismatch found; no Lean or node changes made.
The source statement is correct, so no statement correction/citer audit is
needed. Both docstrings cite Tag 09YY and the blueprint id; the theorem docstring
carries all three proof steps, including the cofinal-tail universal-property
argument. The only proof is the named theorem's `sorry`; there are no definitions,
local notations, private helpers or added axioms. Checked line lengths and exact
verbatim equality of lean.statement with the file signature.

Second-reader validation: server scompile.py compiled the delivered module cleanly
in 1.4 seconds, nice 19, two threads, 60-second per-file limit.
