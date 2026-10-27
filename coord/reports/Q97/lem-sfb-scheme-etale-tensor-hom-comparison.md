## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.scheme_etale_tensor_hom_comparison`
in `Sheaf.AlgebraicGeometry.SchemeEtaleTensorHomComparison`. Its theorem proofs
are `sorry`; both helper definitions have complete data.
No data construction or coefficient ring is replaced by an existence choice. The
item's mathematical statement, statement dependencies and proof plan are unchanged.

Source read: `literature/stacks-project/descent.tex`,
`lemma-equivalence-quasi-coherent-limits` (06VE), especially (7), (8) and their proofs;
`sites-modules.tex`, `lemma-pullback-internal-hom` (0GN2), and
`modules.tex`, `lemma-pullback-internal-hom` (0C6I). These distinguish small étale
from the big site and impose no Noetherian or separation assumption.

Hypothesis and clause correspondence:

- Schemes and sizes: every scheme is explicitly `T : Scheme.{u}`. The site is the
  full `T.Etale`, with objects in `u+1`, arrows in `u`, and regular-function rings in
  `u`. No `EssentiallySmall.{u} T.Etale`, equality of universes, bounded rank,
  Noetherian, affine, or separation hypothesis is imposed.
- The canonical association: `c : ∀ T, ZariskiEtaleModuleContext T` supplies only
  continuity and right-adjoint *proofs*. Its `.extension` is the already recorded
  tensor pullback along epsilon. The dependency theorem supplies such contexts
  and identifies this functor, linearly and naturally, with
  `etaleTensorSectionsSheaf F`, whose sections are Γ(V,V.hom^*F). Thus `c` is not
  an arbitrary equivalence or a new mathematical assumption about T.
- M,N quasi-coherent: `[M.IsQuasicoherent] [N.IsQuasicoherent]` in all tensor and
  Hom clauses. The tensor uses the existing `siteSheafTensorRight` (sectionwise
  tensor followed by sheafification) on the target, and `M ⊗ N` on the source.
- Tensor comparison: `t T M N` is an actual isomorphism, in the displayed
  direction A(M) tensor A(N) -> A(M tensor N).
- Its section formula: the first conjunct sends the sheafified pure tensor of
  `adjunction.unit.app M` and `adjunction.unit.app N` on EVERY Zariski open W
  to the unit image of `tmulSection m n`. Unit images and coefficients generate
  tensor extension locally; hence this normalization uniquely specifies the
  canonical balanced comparison, including arbitrary pulled-back local sections.
- Tensor naturality: the second conjunct is the full commuting square for every
  f:M->M' and g:N->N', using `siteSheafTensorRight.map`,
  `siteSheafTensorSecondMap`, and the source tensor morphism `f ⊗ₘ g`.
- Finite presentation: `[M.IsFinitePresentation]` uses Mathlib's finite local
  free-generator/relation presentation, including rank zero. The family q states
  precisely quasi-coherence of `SheafOfModules.homObj (R := T.sheaf) M N`.
- Hom comparison: h T M N V is a LINEAR EQUIVALENCE from the sections of
  A(Hom(M,N)) on EVERY V to the sections of the existing étale `homObj` on V.
  Its last law is naturality under EVERY site arrow W->V. These data are exactly
  a module-sheaf isomorphism. A single isomorphism in `SmallEtaleModules T` cannot
  express this literally: the generic target Hom has section universe u+1,
  whereas the source sections have universe u. Section equivalences allow both
  universes without altering a single section or assuming a universe equality.
- Canonical evaluation: the next conjunct evaluates h(s) at m on the identity
  object of the slice V. Its right side is A(ev) applied to t(M,Hom(M,N)) of
  the pure tensor m tensor s. The proof q supplies only the Hom's quasi-coherence
  for that tensor comparison. Evaluation fixes the local transformation on every
  further object too, by the restriction law. This is the evaluation comparison,
  and on the image of a Zariski local morphism it is its associated étale morphism.
- Hom naturality: the following conjunct says precomposition by f:M'->M and
  postcomposition by g:N->N' commute with h, using the existing `homObjMap`
  in both the Zariski and étale categories.
- Further-object restrictions: the existing `restrictOverMap` law is retained for
  arrows inside T_et. The added final conjunct quantifies `(U T : Scheme.{u})
  (a : U ⟶ T) [Etale a]`. It takes only the proof `hp` of the canonical pullback
  adjunction and the direct-image comparison `r`, whose values are fixed on every
  open by `gabberPreimageEtaleIso`, exactly as in the cited equivalence. Its
  `p := zariskiEtalePullbackComparison a (c U) (c T) hp r` is the canonical mate.
- Tensor restriction square: `k A B` is the small-etale pullback tensor iso,
  uniquely normalized on tensors of adjunction-unit sections on every T_et
  object, including arbitrary A,B. The next conjunct is the equality of sheaf
  morphisms from A_U(a^*M) tensor A_U(a^*N) to a_et^* A_T(M tensor N):
  `(p_M tensor p_N); k; a_et^*(t_T) = t_U; A_U(schemeTensorIso); p_(M tensor N)`.
  The actual map `schemeEtaleTensorPullbackIso` is constructed from the existing
  monoidal ordinary pullback and its unit-preserving `tensorOrdinaryPullbackIso`.
- Scheme Hom identification: `b` is an iso from a^*Hom(M,N) to
  Hom(a^*M,a^*N), with `b.hom = schemeEtaleHomPullbackMap a M N`. That helper is
  defined in full as `MonoidalClosed.curry` of tensor pullback of evaluation
  composed with the canonical scheme tensor iso. The iso property is precisely
  Stacks 0C6I for flat (here étale) a and finitely presented M. Finite presentation
  of a^*M is supplied by the existing theorem, not an added hypothesis.
- Hom restriction square: `j W` represents a_et^*(h_T) followed by the canonical
  étale Hom base-change iso on every W in U_et. Its full `restrictOverMap` law
  and its evaluation on EVERY section s,m are stated: evaluate using
  `a_et^*(t_T; A_T(ev))` and the unit-normalized `k`. A further explicit formula
  on pullback-unit sections contains `h T M N V` itself and sends evaluation to
  the unit image of `(h_T s)(m)`. Thus j is pinned by the actual pullback pairing,
  rather than an arbitrary iso. The final equality of local module morphisms is
  `h_U(A_U(b)(p_H inverse(s))) = Hom(p_M,p_N inverse)(j(s))`
  for every section s of a_et^*A_T(Hom(M,N)).
  Both sides are compared on ALL U_et objects, including every further slice.

Recorded dependency declarations used (read with their full signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  `Mathlib.CategoryTheory.Sites.Spaces`: `Opens.grothendieckTopology`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale`. The size node is a metatheoretic convention, not a declaration.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes the existing
  `SheafOfModules.IsQuasicoherent`; no coherent or finite-type condition is added.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `Scheme.Modules.etaleTensorSectionsSheaf` (actual pullback sections and restrictions).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction` and the publicly retained `tensorPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`:
  `tensorOrdinaryPullbackIso`, `isQuasicoherent_tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`: `pullbackMonoidal`;
  the existing `Functor.Monoidal.μIso` is transported to tensor-formula pullback.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation`:
  `isFinitePresentation_tensorPullback`.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `ZariskiEtaleModuleContext`, `.extension`, `.adjunction`,
  `smallEtaleModuleRing`, `smallEtaleModulePullback`, `smallEtaleModuleAdjunction`,
  `zariskiEtalePullbackComparison`, `scheme_zariski_etale_quasiCoherent_equivalence`.
  The item imports this original module directly; its published record is retained unchanged.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` publicly exposes
  the recorded independent-universe tensor and `siteSheafTensorRight`,
  `siteSheafTensorTmul`, `siteSheafTensorSecondMap` through
  `SiteTensorFunctoriality` and `TensorProductOfUniverses`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`; its underlying presheaf uses the recorded
  `PresheafOfModules.restrictOverMap`, and has sections the actual local morphisms.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and `.Quasicoherent`:
  `IsFiniteType` and `IsFinitePresentation` (only the latter is hypothesized).
- `WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom`:
  `isQuasicoherent_homObj_of_isFinitePresentation`. The source evaluation is
  `(ihom.ev M).app N`, with the existing scheme closed structure from
  `WeilConjectures.AlgebraicGeometry.Modules.Dual`. `tmulSection` is from the
  existing `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`.

All recorded project proof modules are imported, with proof imports private.
The unstated proof node `lem-sfb-scheme-etale-module-exact-finiteness-comparison`
has no module to import. The Mathlib-matched proof inputs are already exposed
through the imported category/module libraries.

Edge cases checked against the statement and source: empty scheme (all conditions
and empty covers remain meaningful); zero M or N; presentation ranks a=0 or b=0;
infinite-type N; non-Noetherian base; nonseparated base and nonaffine intersections;
identity and arbitrary étale arrows; the object universe u+1 versus section
universe u. Finite presentation is required only in Hom, never in the tensor
comparison. There is no STATEMENT-DISPUTED flag and no mathematical correction.

Searches (through the prescribed msearch wrapper and direct rg):

- LeanFinder: “The equivalence between Zariski and small etale quasi coherent
  modules preserves tensor products and internal Hom of finitely presented
  modules”: eight hits on finite presentation, quasi-coherent data, unrelated
  condensed monoidal structures and the scheme module category; none matches.
- Loogle: `SheafOfModules.homObj, SheafOfModules.tensorObj`: zero hits, service
  reports unknown upstream identifier SheafOfModules.homObj.
- LeanSearch: “Zariski etale comparison preserves tensor products and internal
  Hom of finitely presented modules”: eight results on affine-ring base change,
  module finite presentation and presheaf tensor objects; no site comparison.
- msearch grep: `etale.*[Tt]ensor|[Tt]ensor.*etale|etale.*[Hh]om` under
  Mathlib AlgebraicGeometry: twelve unrelated étale morphism and base-change hits.
- Direct rg under both `lean/WeilConjectures` and `lean/Sheaf`: read the associated
  sheaf, equivalence, tensor functoriality, pullback, internal-Hom and localized
  tensor interfaces. None states this tensor/Hom comparison. Searching the exact
  item id in `WeilConjectures` gives no existing declaration. Searching the helper
  name in both roots also gives no match.

Validation: both files compiled separately in dependency order with scompile.py;
no errors or warnings. The final comparison elaborates in approximately eleven
seconds, within the unchanged sixty-second limit. Its scoped heartbeat allowance
only accommodates elaboration of the full conjunction through tensor localization.

## Dependency modules

H13/H2 is repaired by removing the returned override of
`lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`. The published record,
including its original file and main declaration
`AlgebraicGeometry.Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`,
is retained unchanged. The item now directly imports that original module.
`smallEtaleModuleHasSheafCompose` is moved into the item module and listed only
in the item's `lean.declarations`; its source and blueprint docstring is attached
to this item. There is no delivered dependency module or dependency node delta.
The helper has the same proof-only statement that the return accepted, preserving
coefficient universe u on the full site with object universe u+1.

## Returned delivery repair

Compared with immutable head 2a002a71a9f1, H3 is repaired by the explicit final
conjunct described above: it introduces U, an étale a:U→T, the canonical
`zariskiEtalePullbackComparison`, the tensor restriction square, the canonical
scheme Hom iso and the Hom restriction square. The previous claim that the
internal site restriction law alone expressed these squares has been removed.
H13/H2 is repaired by relocating the helper to this item's module and removing
the dependency record override. No mathematical node field is changed.

## Second reading by Q97

The worker reread the node and the completed signature clause by clause, including
all universes and the actual source and target of each comparison. The initial
attempt to place a single Hom isomorphism in universe u was rejected: it would
identify u+1 with u. The final signature uses the existing homObj's own section
types and a linear equivalence at each object, with every restriction law retained.
The tensor direction, evaluation order M tensor Hom(M,N), variance of f and g,
finite-presentation scope and absence of separation/Noetherian hypotheses were
checked explicitly. The final restriction conjunct was independently reread against the return:
its p has direction A_U(a^*F) → a_et^*A_T(F); the tensor square has the same
source and target on both sides; b has direction a^*Hom → Hom(a^*,a^*);
the Hom square uses p_H inverse on its input and Hom(p_M,p_N inverse) on its
output. j's all-section evaluation and explicit h_T unit formula pin its
meaning as pulled-back h_T. The published dependency record is retained intact.
No independent second worker was started: the dispatcher instructs this worker to
deliver directly, and the maintainer provides the independent review.

Repair-specific sources and searches: reread Modules
`lemma-tensor-product-pullback` and `lemma-pullback-internal-hom` (0C6I), the
full `zariskiEtalePullbackComparison` signature and the equivalence theorem's
normalized r clause. Direct rg searches over `TensorPullback*`,
`Modules/PullbackMonoidal.lean`, `QuasicoherentSheafHom.lean`, and both namespaces
for the new helper names found the existing monoidal ordinary pullback,
`tensorOrdinaryPullbackIso`, quasi-coherence and finite-presentation preservation;
no existing composite tensor-formula Hom pullback map with this name was found.
The helpers use those existing constructions, not new notions or definitions of
tensor product, Hom, or pullback.

Validation in this repair: scompile compiled the final module without errors
or warnings, both as its sandbox module (22.2 s) and under the final module name
(22.6 s). The prescribed deliver2 --no-push dry run printed OK: commit
485e1f05bfd passed preflight and compilation, with exactly the item module, item
node and this report staged. No dependency module or dependency-node override
is included.
