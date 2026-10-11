## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AffinePseudoCoherentCriterion.lean` states
`AlgebraicGeometry.isPseudoCoherent_affine_iff`, with its only proof `by sorry`.
It defines no new notion. The source is Stacks Tag 08E7, Lemma 36.10.2,
pseudo-coherent clause, read at https://stacks.math.columbia.edu/tag/08E7.
The local literature/stacks-project/perfect.tex is absent on this machine.

Hypotheses and clauses, matched individually:

- A ring A: `(A : Type u) [CommRing A]`. Commutativity is implicit in Spec(A)
  and in the source's affine-scheme context; no Noetherian hypothesis is imposed.
- X = Spec(A): every scheme argument is `Spec (.of A)`; X is not an arbitrary scheme.
- M is a complex of A-modules: `(M : CochainComplex (ModuleCat.{u} A) ℤ)`.
  No boundedness or finiteness is required of M.
- E is the associated derived object: the left side's argument is
  `DerivedCategory.Q.obj` of `Functor.mapHomologicalComplex` applied to
  `tilde.functor (.of A)` and M. The explicit zero-preservation instance is
  `⟨fun _ _ ↦ tilde.map_zero⟩`. The target category is the shared
  `SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)`, rather than
  the distinct Scheme.Modules category instance.
  The comparison natural isomorphism in `exists_affineQCohDerivedEquivalence`
  identifies exactly this termwise construction with the affine equivalence
  applied to Q(M), followed by the quasi-coherent full-subcategory inclusion.
  Thus E is specified directly, and no unrelated equivalence is quantified over.
  Quasi-coherent cohomology is automatic for this construction, not an extra
  hypothesis to be imposed on M.
- E is pseudo-coherent: `Scheme.IsPseudoCoherent (Spec (.of A))` of this object,
  using the recorded local finite-free definition unchanged.
- If and only if: `↔`, giving both directions without any extra conjuncts.
- M is quasi-isomorphic to a bounded-above finite free complex:
  `DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M)`.
  The already landed definition expands to existence of a complex P and b,
  `P.IsStrictlyLE b`, `∀ j, Module.Free A (P.X j) ∧ Module.Finite A (P.X j)`,
  and `Nonempty (Q.obj P ≅ Q.obj M)`. Strict support above b is termwise
  boundedness, not merely cohomological boundedness. The isomorphism is in
  D(A), so expresses quasi-isomorphism without demanding a direct chain map
  from the original arbitrary complex M.
- The HasDerivedCategory binders explicitly supply the categories appearing
  in the statement and in restriction to opens. `wA` and `wX` are independent
  morphism universes; the open restrictions use the same wX as required by
  the recorded scheme pseudo-coherence definition. These are construction
  infrastructure, not additional geometric assumptions. All universes and
  mathematical variables are explicitly bound; no auto-implicit variables.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` (its locally
  affine locally ringed space structure and docstring), instantiated at Spec(A).
- Sheaf.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory` and their full
  definitions/docstrings, via the pseudo-coherence import and carrier.
- Sheaf.AlgebraicGeometry.PseudoCoherentComplex:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, used directly.
- Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence:
  `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`, read in full;
  its first natural isomorphism gives the identification just explained.
  This theorem is not imported because the signature uses its explicit
  termwise tilde construction rather than a choice of the existential equivalence.
- Mathlib.AlgebraicGeometry.Modules.Tilde: `AlgebraicGeometry.tilde.functor`
  and `AlgebraicGeometry.tilde.map_zero`, used directly.
- Sheaf.RingTheory.RingPseudoCoherent: `DerivedCategory.IsPseudoCoherent`,
  used directly; its full definition and docstring were read. Its existing
  node `def-pc-ring-pseudo-coherent-complex` is added to stmt_deps under
  brief-stage2 section 5 / STATE's STMT_DEPS MAY GAIN LANDED NODES rule.
  This is an existing landed definition, not a new node or statement correction.

Edge cases checked mathematically before writing: the zero complex has the
zero finite free model; the zero ring has empty spectrum and every A-module
is zero, so both sides hold. Ranks can be zero, the upper bound can be any
integer, and there is no lower bound (infinitely many negative-degree terms
are permitted). Arbitrary characteristic and non-Noetherian rings are
included. No nonempty cover or Nontrivial ring hypothesis was added.

Searches (msearch.py, group F1, item lem-pc-affine-pseudo-coherent-criterion):

- leanfinder: "A complex on Spec A is pseudo coherent if and only if the module
  complex is quasi isomorphic to a bounded above complex of finite free modules".
  Eight hits, general derived support/representative lemmas including
  DerivedCategory.isGE_Q_obj_iff and exists_iso_Q_obj_of_isLE; no affine criterion.
- loogle: "IsPseudoCoherent". Zero hits; unknown identifier in Mathlib.
- grep: "pseudo[Cc]oherent|[Pp]seudo.[Cc]oherent", Mathlib AlgebraicGeometry.
  Zero hits.
- leansearch: "pseudo coherent complex affine scheme finite free bounded above".
  Unavailable, Internal Server Error; no mathematical verdict inferred.
- rg in WeilConjectures for pseudo-coherence and the item id: only an informal
  mention in Cohomology/DirectImage/FiniteFreeComplex.lean:124; no declaration
  of this criterion and no item-id match.
- rg in lean/Sheaf for pseudo-coherence: found the shared scheme and ring
  definitions and related statements; none states this affine criterion.
- rg for the proposed full name `isPseudoCoherent_affine_iff` in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no matches.

The source and node agree. No statement dispute or correction is needed.
The theorem docstring includes all four natural-language proof steps and
names each tool node used, ready for stage 3.

Validation: server scompile.py returned exit code 0, compiled in 4.9 seconds,
with no warnings or errors. The delivery dry run is run after recording the
signature and this report. No second-reading section is written by this worker.


## Second reading by F1

Independent second reading, 2026-10-12. I opened the sandbox node and module,
every statement-dependency node, and the source declarations in Scheme.lean,
DerivedCategory.lean, PseudoCoherentComplex.lean, RingPseudoCoherent.lean,
AffineQCohDerivedEquivalence.lean and Mathlib Modules/Tilde.lean. The local
Stacks checkout is absent. I read the actual Stacks perfect.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex,
including its chapter conventions and lemma-pseudo-coherent-affine, and
cross-checked https://stacks.math.columbia.edu/tag/08E7. The source assumes
an affine scheme over a commutative ring, without Noetherian, field,
nonzero-ring, or boundedness assumptions. This node takes only the
pseudo-coherent clause, not the separate fixed-m clause of that lemma.

Objects, hypotheses and conclusion, checked item by item:

1. A is a ring: `(A : Type u) [CommRing A]`. Correct: commutativity is
   required by Spec and explicit in def-pc-scheme; no extra finiteness,
   characteristic, domain, or Noetherian assumption occurs.
2. X is Spec(A): every occurrence is `Spec (.of A)`. Correct: the scheme is
   fixed by A rather than introducing an independent scheme or a base map.
   Mathlib Scheme's locally affine locally ringed space structure is the
   recorded dependency notion.
3. M is an arbitrary complex of A-modules:
   `(M : CochainComplex (ModuleCat.{u} A) ℤ)`. Correct: integer cochain
   degrees and no restriction on the input complex or its cohomology.
4. E is the corresponding object under the affine equivalence:
   `DerivedCategory.Q.obj` of the termwise
   `Functor.mapHomologicalComplex` of `tilde.functor (.of A)` applied to M.
   Correct: I compared this expression with the first natural-isomorphism
   clause of `exists_affineQCohDerivedEquivalence`. That clause identifies
   exactly this composite with `Q ⋙ e.functor ⋙ schemeDerivedQCohProperty.ι`.
   The explicit target is the same SheafOfModules category used by
   schemeDerivedCategory, avoiding Scheme.Modules' different category
   instance. The explicit map-zero witness is Mathlib's tilde.map_zero.
   Quasi-coherent cohomology follows for every such M; no extra hypothesis
   or independent choice of equivalence is needed. An additional binder E
   and equality hypothesis would only rename this specified object.
5. The left clause is E pseudo-coherent:
   `Scheme.IsPseudoCoherent (Spec (.of A)) (...)`. Correct: its dependency
   definition says every point has an open neighbourhood with an isomorphic
   bounded-above complex of finite rank free sheaves. The upper bound is
   termwise and the rank may depend on the degree, as the node requires.
6. The connective is iff: `↔`. Correct: neither direction is omitted and
   there is no additional conjunct.
7. The right clause is quasi-isomorphism to a bounded-above finite free
   complex: `DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M)`.
   Correct: I unfolded the recorded ring-level definition. It quantifies
   `∃ (E : CochainComplex ...) (b : ℤ)`, requires `E.IsStrictlyLE b`,
   requires `Module.Free A (E.X j) ∧ Module.Finite A (E.X j)` for every j,
   and requires `Nonempty (Q.obj E ≅ Q.obj M)`. Mathlib's
   `CochainComplex.isStrictlyLE_iff` identifies the bound with vanishing
   of terms above b. Finite and free together mean finite free, rather
   than finite projective; the derived isomorphism expresses the required
   quasi-isomorphism without demanding a particular direct chain map.
8. Infrastructure: the three HasDerivedCategory binders supply D(A),
   D(O_X), and its open restrictions, exactly as the shared definitions
   require. The two morphism universes wA and wX are independent; all open
   restrictions use wX. These specify localization constructions and do
   not impose additional geometric properties. All variables and universes
   are bound. ModuleCat.{u} matches the affine-equivalence dependency's
   universe convention for A : Type u, with u arbitrary.

Edge cases: zero complexes and zero-rank terms are included. A zero ring
is allowed: its spectrum is empty, the local left condition is vacuous,
and every module over it is zero, so the right condition holds as well.
The empty finite standard-open cover in the natural-language converse is
compatible with this case; the theorem has no Nonempty index hypothesis.
There is no fixed natural n or fixed rank to exclude n = 0. There is no
lower degree bound, and any integer upper bound is permitted. All
characteristics and non-Noetherian rings are covered. Universes impose
no field, dimension, or cardinal finiteness assumption.

Independent searches, using different wording from the first reader:

- msearch leanfinder: "Associated sheaf functor detects existence of a finite
  rank free bounded above resolution on an affine spectrum". Eight hits,
  all sheaf finite-type/presentation or generator results; none is this
  derived affine criterion.
- msearch loogle: `"PseudoCoherent"`. Zero hits.
- msearch grep in Mathlib AlgebraicGeometry:
  `pseudo.?coherent|finite.?free.*bounded`. Zero hits.
- msearch leansearch: "A module complex has a bounded above finite free
  representative exactly when its associated sheaf complex on Spec is
  pseudo coherent". Service unavailable (Internal Server Error), recorded
  as unavailable, with no inference of mathematical absence.
- Independent rg in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for `pseudo.?coherent`,
  `affine.*finite.?free` and `isPseudoCoherent_affine_iff`: upstream has
  only an informal pseudo-coherence mention in FiniteFreeComplex.lean
  and unrelated finite-free base-change statements. The project has the
  shared ring and scheme predicates and related results (including
  AffinePseudoCoherentLift and PseudoCoherentQCoh), but no existing
  declaration of this criterion. The proposed name has no collision.

No H3 or H4 mismatch found. The extra stmt_dep names the already landed
ring predicate used verbatim; it introduces no new notion. There are no
new definition nodes, dependency modules, or statement correction to
review. The module has no definitions or private copies, and its only
proof is the required sorry. Its module and theorem docstrings name the
source and blueprint id; the theorem records all four node proof steps,
including tilde compatibility, the finite standard-open cover, lifting
local finite-free differentials, and ring localization gluing. No
mathematical statement, Lean code, or node signature was changed. This
second reading appends only the independent review to the report.

Validation: fresh scompile.py compilation returned exit code 0 in 5.1 s,
with no warnings or errors. Independently checked that lean.statement is
the file signature verbatim after whitespace normalization, and all Lean
lines are at most 100 characters. The delivery dry run follows.
