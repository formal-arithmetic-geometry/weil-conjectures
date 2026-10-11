## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleInfinitesimalNeighbourhoods.lean`
states `AlgebraicGeometry.etale_on_open_of_etale_infinitesimal_neighbourhoods`.
It uses a morphism `g : X ⟶ S`, a closed immersion `i : Z ⟶ S`, the
locally Noetherian target, finite type (`LocallyOfFiniteType` and
`QuasiCompact`) hypotheses, and an ideal sheaf `J` identified with `i.ker`.
The nth infinitesimal neighbourhood is represented by the Mathlib ideal
sheaf subscheme `(J ^ (n + 1)).subscheme` and its structure map
`(J ^ (n + 1)).subschemeι`; its base change is represented by
`pullback g ((J ^ (n + 1)).subschemeι)`, with map to the neighbourhood
`pullback.snd g ((J ^ (n + 1)).subschemeι)`. The hypothesis `h_etale` says
this map is étale for every `n : ℕ`. The conclusion gives an open subscheme
`W : X.Opens` containing the inverse image of the closed subscheme,
expressed as `(g : X → S) ⁻¹' Set.range (i : Z → S) ⊆ (W : Set X)`, and says
that `W.ι ≫ g` is étale.

The first two typeclass hypotheses render “between locally Noetherian schemes”
and “of finite type” exactly: `IsLocallyNoetherian S`, `LocallyOfFiniteType g`,
and `QuasiCompact g`. The `[IsClosedImmersion i]` hypothesis renders that
`Z` is a closed subscheme. `hJ : J = i.ker` identifies the supplied ideal
sheaf with the closed immersion's ideal sheaf. The universal quantified
clause `∀ n : ℕ, Etale (pullback.snd g ((J ^ (n + 1)).subschemeι))` renders
étaleness on every infinitesimal neighbourhood, including `n = 0`. The
existential conclusion and its conjunction render respectively the open
neighbourhood, containment of all points over `Z`, and étaleness on that
open.

Dependencies used: `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` from Mathlib.AlgebraicGeometry.Morphisms.FiniteType
and QuasiCompact; `AlgebraicGeometry.IsLocallyNoetherian` from
Mathlib.AlgebraicGeometry.Noetherian; `AlgebraicGeometry.Etale` from
Mathlib.AlgebraicGeometry.Morphisms.Etale; the base-change convention node
`def-pc-base-change` is represented by Mathlib's `CategoryTheory.Limits.pullback`
and `pullback.snd`, recorded in `Sheaf.AlgebraicGeometry.BaseChangeConventions`;
`def-sbc-ideal-sheaf-powers` is Mathlib's `Scheme.IdealSheafData` multiplication
and powers; `def-sbc-closed-immersion-ideal-sheaf` is Mathlib's
`Scheme.Hom.ker`; and the closed-subscheme constructor is
`Scheme.IdealSheafData.subscheme`/`subschemeι`.

Edge cases checked: `n = 0` gives the closed subscheme cut out by `J`; the
universal quantifier includes all natural numbers; if the inverse image of
`Z` is empty, the conclusion permits `W = ⊥`; and no nonempty or separated
assumption was added. The ideal sheaf is allowed to be zero or nilpotent.

Searches made before writing: `msearch.py leanfinder` query “morphism etale at
points over closed subscheme if etale on all infinitesimal neighbourhoods”
returned only `IsEtale`, `Algebra.Etale.formallyEtale`, `Scheme.Etale`, and
`RingHom.Etale.propertyIsLocal`, with no criterion. `msearch.py loogle` was
queried for `IsEtale, Algebra.Etale.formallyEtale, Scheme.Etale,
RingHom.FormallyEtale, RingHom.Etale`; no exact infinitesimal-neighbourhood
criterion was found. `msearch.py grep` searched Mathlib AlgebraicGeometry for
`thickening|infinitesimal neighbo` and the Etale directory; it found only
`FormallyUnramified.lean` and `RingTheory/Etale/Locus.lean`, neither matching.
`rg` searched the source and `lean/Sheaf` for the node id and keywords; no
existing declaration of this criterion was found. The recorded node searches
also report no match. The Mathlib declarations used above were checked in their
source signatures and docstrings.

## Second reading by G1

I independently read the sandbox node, module and worker report, every statement
node in `stmt_deps`, the recorded Mathlib declarations, and the landed
`BaseChangeConventions.lean`. No new nodes, dependency modules or statement
correction are present or needed. The original node statement and its Lean
signature are unchanged.

Source check: the repository does not contain the fetched Stacks .tex files.
I read the available Stacks .tex copy at
`/home/ubuntu/c1-stacks-review/more-morphisms.tex`, lines 3670–3695
(label `lemma-check-smoothness-on-infinitesimal-nbhds`, part (2)), its
Artinian lifting criterion at lines 3574–3610, and its infinitesimal-neighbourhood
construction at lines 672–691. The lemma assumes a finite type morphism between
locally Noetherian schemes and a closed subscheme; there are no additional
standing hypotheses. I also read `morphisms.tex`, lines 8057–8100,
Definition 02GI and Lemma 02GJ: étale at a point means étale on a source
neighbourhood, and étaleness is local on the source. The node's common open W
is exactly the union of those neighbourhoods. The powers convention gives
Z_n cut out by J^(n+1), with Z_0 = Z.

Object, hypothesis and conclusion checklist (all verdicts: exact):

- X and S schemes and g : X -> S: `{X S : Scheme.{u}} (g : X ⟶ S)`.
  These are arbitrary schemes, not affine schemes or schemes over a field.
- Finite type g: `[LocallyOfFiniteType g] [QuasiCompact g]` is exactly
  `def-weil-finite-type-morphism`. I opened both classes in FiniteType.lean
  and QuasiCompact.lean: the affine finite-generation condition and compact
  inverse images of open compact sets give the node's two clauses.
- Both X and S locally Noetherian: `[IsLocallyNoetherian S]` supplies S;
  X follows by `LocallyOfFiniteType.isLocallyNoetherian g`
  (Noetherian.lean:239). This is a theorem, not an automatically synthesized
  instance; a stage-3 proof can install it. Thus omitting a redundant X binder
  drops no hypothesis. The report's original explanation did not make this
  implication explicit. The class at Noetherian.lean:57 is the recorded
  `pqf-def-locnoeth` notion, equivalent to an affine Noetherian cover.
- Closed subscheme Z of S: `{Z : Scheme.{u}} (i : Z ⟶ S)
  [IsClosedImmersion i]`. A closed immersion presents exactly a closed
  subscheme, including its nonreduced structure; range is used only for
  its underlying set in the conclusion.
- Its quasi-coherent ideal J: `(J : S.IdealSheafData) (hJ : J = i.ker)`.
  Basic.lean:65 defines affine ideals compatible with localization;
  this is precisely quasi-coherent ideal-sheaf data, not an arbitrary
  non-quasi-coherent ideal subsheaf. `Hom.ker` at Basic.lean:692 and
  `Hom.ker_apply` at :702 give the actual kernel on affine opens because
  a closed immersion is quasi-compact. hJ identifies the supplied ideal;
  it is not an added vanishing or finiteness assumption.
- For every n >= 0, Z_n is cut out by J^(n+1):
  `(J ^ (n + 1)).subscheme` with structure map
  `(J ^ (n + 1)).subschemeι`. Basic.lean:416–425 defines powers affinewise
  and `ideal_pow` gives J(U)^(n+1). Subscheme.lean constructs the scheme
  from Spec(Γ(S,U)/J(U)^(n+1)); its `ker_subschemeι` recovers that ideal.
- X_n = Z_n ×_S X and the map to Z_n:
  `pullback g ((J ^ (n + 1)).subschemeι)` and `pullback.snd g ...`.
  The opposite order of factors is canonically isomorphic over Z_n,
  so the étaleness condition is identical. The recorded base-change
  module explicitly identifies the base change as `pullback f T.hom`
  and its target projection as `pullback.snd`. The module's primary
  declaration `moduleBaseChange` concerns modules and is not needed here;
  using the already existing Mathlib pullback introduces no private notion.
- Étaleness for every n: `(h_etale : ∀ n : ℕ, Etale (pullback.snd ...))`.
  The class in Etale.lean:41 is the recorded `def-weil-etale-morphism`;
  it is affine-local ring-map étaleness, with no separatedness assumption.
- Existence of an open source subscheme W: `∃ W : X.Opens`.
- It contains every point over Z:
  `(g : X → S) ⁻¹' Set.range (i : Z → S) ⊆ (W : Set X)`.
  This takes the scheme-theoretic closed immersion's underlying image;
  it does not replace Z by a different closed subscheme for the hypotheses.
- Étaleness on that W: `Etale (W.ι ≫ g)` is precisely g|_W,
  conjoined with containment after the same existential quantifier.

Edge cases: all natural numbers are quantified, including n = 0 (J^1 = J).
If Z is empty, J is the unit ideal and every Z_n is empty; the conclusion
allows W = the empty open. If X or S is empty, no nonemptiness binder blocks
it. If the ideal is zero, Z_0 identifies with S and the n = 0 hypothesis
already says g is étale; W can be the whole source. Nilpotent ideals are
allowed. No index set, coefficient object or characteristic is introduced,
so there is no excluded characteristic or zero object. Universe u is explicit
and arbitrary; the common Scheme.{u} ambient category is Mathlib's scheme
morphism/pullback convention, and schemes of different small sizes can be
placed in a common universe. There is no test-object quantifier in an
independent smaller universe. Every variable in the signature is bound.

Independent searches, using different wording from the first reader:

- `msearch.py ... leansearch "Etaleness from all powers of an ideal defining
  a closed subscheme"`: service unavailable (Internal Server Error), recorded
  as unavailable, not as a negative search result.
- `msearch.py ... leanfinder "An etale morphism criterion using reductions
  modulo every power of a closed subscheme ideal"`: eight hits including
  `Algebra.mem_etaleLocus_iff`, `Algebra.basicOpen_subset_etaleLocus_iff`,
  `Algebra.exists_etale_of_isEtaleAt`, and formal étaleness instances.
  They concern an algebra's étale locus or the lifting property, and do
  not state the all-infinitesimal-neighbourhood criterion.
- `msearch.py ... loogle "AlgebraicGeometry.Etale,
  CategoryTheory.Limits.pullback.snd"`: `Etale.instSndScheme` (base-change
  preservation in the other direction) and
  `exists_etale_isCompl_of_quasiFiniteAt` (a separated quasi-finite
  neighbourhood result). Neither is this criterion.
- `rg` over pinned Mathlib AlgebraicGeometry and RingTheory/Etale,
  the entire upstream WeilConjectures tree, and repository lean/Sheaf
  for `infinitesimal.*(nbhd|neigh)|etale.*infinitesimal|
  étale.*infinitesimal|infinitesimal.*(etale|étale)` found no declaration
  of the criterion. The only project occurrence was a proof citation
  in FiniteEtaleLiftingComplete.lean. A broader neighbourhood search
  yielded unrelated neighbourhood lemmas, and the Mathlib occurrence
  referred to the ring-level formal lifting definition.

Mismatches and repairs: H8, the theorem docstring gave only four proof
keywords and omitted the node's actual six-step argument. Replaced that
paragraph with all six steps, including factorization via a nilpotent
Artinian maximal ideal, the square-zero small extension, projection of
its lift, the residue-field fibre comparison, shrinking at each point,
and the union of neighbourhoods; dependency IDs are cited at each step.
H9, added the conventional copyright/license/author header, moved the
module docstring immediately after imports, removed the redundant
`open AlgebraicGeometry` before entering that namespace, and removed
`IdealSheaf.Functorial`, whose comap/map API the statement never uses.
The retained imports provide subschemes, étaleness, finite type,
Noetherianity and scheme pullbacks. No hollow definition is introduced;
there is just one named theorem with its proof exactly `by sorry`.
The node's lean.statement still equals the complete signature verbatim.

Validation: compiled the repaired delivery module using scompile.py on
G1's server sandbox; the result is recorded below before delivery.

Server result: exit code 0, compiled in 1.7 seconds, no errors or warnings.
Signature equality and the 100-character line limit were checked locally.
