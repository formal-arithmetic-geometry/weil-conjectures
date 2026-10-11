## Worker report

The module `Sheaf.AlgebraicGeometry.QuasicoherentSheafHom` states
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_homObj_of_isFinitePresentation`.
Its only proof is `sorry`; it introduces no definitions, extra nodes, or dependency modules.
The node is unchanged except for its `lean` field.

Clause-by-clause correspondence:
- “Let X be a scheme”: `(X : Scheme.{u})`, with the universe explicitly declared.
- “G an O_X-module”: `(G : X.Modules)`.
- “of finite presentation”, clause (2) of the dependency: `[G.IsFinitePresentation]`.
  Mathlib defines this by a covering with finite free presentations; its
  `presentationOfIsCokernelFree` and `Presentation.isColimit` give the exact
  cokernel formulation of that dependency.
- “F a quasi-coherent O_X-module”: `(F : X.Modules) [F.IsQuasicoherent]`.
  The recorded `pqf-def-coherent` module explicitly uses this Mathlib class for
  quasi-coherence. Its separate `RingedSpace.IsCoherent` predicate is not needed.
- “the sheaf Hom Hom(G,F), with sections Hom(G|_W,F|_W)”: the conclusion uses
  `SheafOfModules.homObj (R := X.sheaf) G F`, precisely the recorded dependency.
  Its source definition uses the internal Hom presheaf and its sheaf proof;
  restriction is to the localized site over W, equivalent to opens of W.
  The scalar action is the existing commutative-ring sheaf Hom action.
- “is a quasi-coherent O_X-module”: `.IsQuasicoherent` on that same Hom object.

Dependencies read and used:
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` in
  `Mathlib.AlgebraicGeometry.Scheme` (imported through Modules.Sheaf).
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`; `Scheme.Modules` specializes it to
  the underlying ring sheaf of `X` in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `def-weil-pbc-module-finite-type-presentation`: the Mathlib leaf's
  `SheafOfModules.IsFinitePresentation` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. Read the class,
  finite Presentation, QuasicoherentData and cokernel conversion declarations.
  The finite-type clause uses `SheafOfModules.IsFiniteType` in Generators;
  the item uses only clause (2).
- `pqf-def-coherent`: read `Sheaf.AlgebraicGeometry.Coherent` and its
  `AlgebraicGeometry.RingedSpace.IsCoherent` signature/docstring. As that module
  explicitly specifies, its quasi-coherent clause is the Mathlib
  `SheafOfModules.IsQuasicoherent` class in Quasicoherent, used directly here.
  No unused import of the coherent-kernel predicate is added.
- `def-pur-sheaf-hom`: `SheafOfModules.homObj` in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; read its full
  signature, module/declaration docstrings, underlying construction and
  `homObjSectionsEquiv`.

Source check: local `literature/stacks-project` is absent on this machine.
Opened https://stacks.math.columbia.edu/tag/01LA (item (10)) and
https://stacks.math.columbia.edu/tag/01CQ (statement and proof). The source
matches this node; finite presentation already implies quasi-coherence of G,
so no redundant additional quasi-coherence assumption on G is necessary.
The theorem docstring carries all four DAG proof steps, including the
restriction/cokernel argument, finite sums at zero rank, matrix kernel
identification on every subopen, and affine refinement/locality.

Edge cases checked mathematically: the empty scheme requires no point or
nonempty hypothesis; G = 0 or F = 0 gives zero internal Hom; finite ranks
m = 0 or n = 0 are allowed by the existing finite-presentation class and the
kernel calculation; arbitrary schemes are allowed without Noetherian,
affine, separated or characteristic assumptions. Universe u is explicit,
and Hom over the opens site stays in u (`max u 0 u = u`). No index universe,
chosen presentation, or open neighbourhood is added to the signature.

Searches (2026-10-11):
- `msearch.py leansearch`, query “sheaf Hom finitely presented quasi coherent”:
  service unavailable (Internal Server Error); recorded as unavailable.
- `msearch.py leanfinder`, query “sheaf Hom from a finitely presented module
  into a quasi-coherent module is quasi-coherent”: eight hits, all on finite
  presentation implying quasi-coherence or its presentation data. None states
  quasi-coherence of internal Hom.
- `msearch.py loogle`, query
  `SheafOfModules.homObj, SheafOfModules.IsQuasicoherent`: zero hits, unknown
  identifier homObj (which is in the source project, not Mathlib).
- `msearch.py grep`, regex `homObj|internalHom|sheafHom` in
  `Algebra/Category/ModuleCat/Sheaf`: zero Mathlib hits.
- `rg` in the source project's module-sheaf directory and project
  `lean/Sheaf/AlgebraicGeometry`: found the recorded InternalHom construction,
  its monoidal uses, the stronger coherent-Hom lemma, and unrelated specialized
  Hom lemmas; no exact theorem. The coherent-Hom theorem requires coherent F
  and thus cannot realize the quasi-coherent statement here.
- `rg` across the source `WeilConjectures`, Mathlib, and `lean/Sheaf` for
  `isQuasicoherent_homObj|homObj.*IsQuasicoherent|IsQuasicoherent.*homObj`: no hits.
- `rg` for the exact item id in source `WeilConjectures`: no hits.

No statement dispute or correction was needed.

## Second reading by E1

Independently read the node copy and `QuasicoherentSheafHom.lean`, then opened
all five statement-dependency nodes and their recorded source declarations.
No mathematical or Lean mismatch was found; no statement, module, dependency,
or node field needed changing. This section is the only review edit.

The complete object/hypothesis/conclusion list and correspondence is:
1. Scheme X: `(X : Scheme.{u})` is Mathlib's locally ringed space with local
   affine neighbourhoods (`Scheme.lean`, structure Scheme). Verdict: exact.
2. O_X-module G: `(G : X.Modules)`, where `Scheme.Modules` is
   `SheafOfModules.{u} X.ringCatSheaf`. Verdict: the recorded module-sheaf
   category, not modules over global sections or stalks.
3. G of finite presentation, dependency clause (2): `[G.IsFinitePresentation]`.
   Read `Presentation`, `Presentation.IsFinite`, `QuasicoherentData`, and
   `IsFinitePresentation` in Mathlib's Quasicoherent module. The class requires
   an open covering with finitely many generators and relations;
   `presentationOfIsCokernelFree` and `Presentation.isColimit` relate this
   precisely to the node's finite free cokernel presentations. Verdict: exact.
4. O_X-module F: `(F : X.Modules)` uses the same ring sheaf and category as G.
   Verdict: exact; no implicit change of coefficient ring.
5. F quasi-coherent: `[F.IsQuasicoherent]`. Read the class (local free
   presentations) and `Sheaf.AlgebraicGeometry.Coherent`'s explicit designation
   of this existing class for the quasi-coherent clause of pqf-def-coherent.
   On schemes this is the affine-local tilde-module notion. Verdict: exact;
   coherence or Noetherian hypotheses are not substituted for quasi-coherence.
6. Sheaf Hom(G,F), with sections Hom(G|_W,F|_W):
   `SheafOfModules.homObj (R := X.sheaf) G F`. Read its full source signature,
   sheaf construction, and underlying `PresheafOfModules.homObj`,
   `restrictOver`, `restrictOverMap`, and scalar action. Over W its module is
   the linear morphisms on `Over W`; on the opens site this is restriction to
   W, and restriction/scalars are exactly those of def-pur-sheaf-hom.
   Verdict: exact, including the explanatory sections clause through the
   definition rather than an additional conclusion about a different object.
7. Conclusion: `.IsQuasicoherent` on that very Hom object. Verdict: exact.
   All objects are universally quantified before the two hypotheses; no
   presentation, neighbourhood, base field, or additional instance is assumed.

Source reading: the local Stacks checkout is absent. Read the source TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex
at `section-quasi-coherent`, including its introductory assumption and item
(10), and modules.tex at `lemma-internal-hom-locally-kernel-direct-sum` (01CQ).
The scheme section assumes only that X is a scheme. Its extra description of
G as quasi-coherent follows from finite presentation, as also witnessed by
Mathlib's `instIsQuasicoherentOfIsFinitePresentation`; it is not a missing
hypothesis. The ringed-space kernel lemma has no further ambient assumption.
Also opened https://stacks.math.columbia.edu/tag/01CQ. The web fetch of 01LA
failed, so the source TeX, successfully retrieved independently, was used.

Edge cases: the signature admits the empty scheme (Scheme's existing empty
construction has a vacuous local-affine condition). Zero G or zero F gives
zero Hom. Presentation indices may be empty because their only restriction
is `Finite`, not `Nonempty`; m = 0 and n = 0 are covered. There is no field,
characteristic, separatedness, affineness, or Noetherian assumption. The
explicit universe u covers any scheme universe; opens have object universe u
and thin hom universe 0, so the internal Hom's `max u 0 u` equals u. No
independent small universe or unbound variable occurs.

Independent searches used different wording from the first reader:
- LeanFinder via msearch: "quasicoherence of the module of local linear
  morphisms with finitely many generators and relations". Eight hits, all
  presentation data or finite-presentation consequences; no Hom theorem.
- Loogle via msearch: `SheafOfModules.IsQuasicoherent,
  SheafOfModules.IsFinitePresentation`. One hit, finite presentation implies
  quasi-coherence of the same module; not this two-module theorem.
- LeanSearch via msearch: "internal hom sheaf quasi coherent finite
  presentation source module". Service unavailable (Internal Server Error),
  recorded as unavailable, with no negative verdict assigned to it.
- `rg -i` for `(hom|dual).*(quasicoherent|quasi.coherent)` and its reverse in
  Mathlib's module-category and algebraic-geometry module directories,
  the entire source `WeilConjectures`, and repository `lean/Sheaf`. Results
  concern pushforward, morphisms, derived Hom, or coherent Hom, not this
  theorem. Opened `CoherentSheafHom.isCoherent_homObj`: both inputs must be
  coherent and the conclusion is coherence, so it is not the same statement.
- Exact declaration and blueprint-id search in `dag/lean_names_upstream.json`
  and the source `WeilConjectures` returned no match.

There are no new definition nodes, dependency modules, or statement
corrections to review. The module introduces no definition and has exactly
one theorem with `sorry`. Its source/blueprint docstrings reproduce all four
proof steps: local cokernel presentation and restriction; finite sums
including rank zero; restriction-compatible matrix-kernel identification;
and affine refinement/locality. Imports and namespace use existing notions,
and the node's `lean.statement` is the file signature verbatim.
