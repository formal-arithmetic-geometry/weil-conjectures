## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` states the node in
`AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite`, with only `sorry` as
proof. Its companion `isCoherent_unit_of_finite_to_locallyNoetherian` supplies precisely the
parenthetical example's coherence hypothesis. No definition is introduced; no node correction
or additional dependency module is needed.

Hypotheses and clauses:

- Schemes and the morphism `f : Y → X`: `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
- Finite morphism: `[IsFinite f]`, the declaration recorded by
  `def-weil-finite-integral-morphism`.
- Locally Noetherian target: `[IsLocallyNoetherian X]`, recorded by `pqf-def-locnoeth`.
- An O_Y-module: `(F : Y.Modules)`; coherent: `(hF : RingedSpace.IsCoherent Y.toRingedSpace F)`.
  This uses exactly the recorded `pqf-def-coherent` definition. `Y.Modules` and its
  `SheafOfModules.{u} (moduleRings Y.toRingedSpace)` argument carrier are definitionally equal.
- Coherent O_X-direct image: `RingedSpace.IsCoherent X.toRingedSpace ((pushforward f).obj F)`.
- Every affine open U: `∀ (U : X.Opens), IsAffineOpen U → ...`; the intrinsic ring is
  `Γ(X, U)`. Any presentation U = Spec R identifies R canonically with this ring. The affine
  preimage and its coordinate ring are already part of `[IsFinite f]`; no chosen presentation
  or additional hypothesis is necessary.
- Section equality: `Γ((pushforward f).obj F, U) = Γ(F, f ⁻¹ᵁ U)`. These are the underlying
  abelian-group objects; this is precisely Mathlib's `pushforward_obj_obj` equality.
- Finite R-module: `Module.Finite Γ(X, U) Γ((pushforward f).obj F, U)`. The existing section
  module instance restricts scalars along `(f.app U).hom`, so this is the intended action,
  rather than an arbitrary R-module structure on the same carrier.
- The example F = O_Y: the companion theorem concludes
  `RingedSpace.IsCoherent Y.toRingedSpace (SheafOfModules.unit Y.ringCatSheaf)` with exactly
  the same finite and locally Noetherian hypotheses. Substituting this module and proof in
  the main theorem gives the entire example, including finite sections.
- The final parenthesis explicitly excludes higher-direct-image vanishing; it is not included.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, its docstring,
  full signature and `finite_app` field (finite = affine with finite maps on affine opens).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`, full
  signature and docstring (all affine section rings Noetherian), equivalent to the recorded
  affine-cover form of `pqf-def-locnoeth`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`, full
  definition and docstring, including finite type and kernels of finite free maps on all opens.
- `Sheaf.AlgebraicGeometry.TensorPullback`: read the recorded `tensorPullback` and its
  `nonempty_tensorPullbackAdjunction` signatures and docstrings. Its right adjoint is exactly
  Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforward`, used here. This statement uses
  only that direct image, not tensor pullback, so the unused tensor-pullback import is omitted.
  `Mathlib.AlgebraicGeometry.Modules.Sheaf` is already imported by Coherent; its `pushforward`
  and `pushforward_obj_obj` signatures and section module instance were read in full.

Source check: the local literature checkout is absent on this machine. Read the official
[Stacks 01Y6](https://stacks.math.columbia.edu/tag/01Y6) and
[Stacks 01XZ](https://stacks.math.columbia.edu/tag/01XZ). The former assumes quasi-coherence
and concludes coherence for coherent F; coherence itself implies quasi-coherence (01XZ's
proof, which points to Modules 01BW and 01BO), so no extra hypothesis is required. The
module docstring carries all eight steps of the node and their dependency ids. The companion
carries step 8, proving coherence of O_Y from finite-over-Noetherian affine charts.

Edge cases checked: empty schemes and the empty affine open are admitted without nonemptiness
hypotheses. The empty open has zero section modules, hence finite sections. The zero coherent
module is admitted. No surjectivity, flatness, properness, affine target, finite-rank hypothesis
or field characteristic is imposed. An arbitrary scheme universe `u` is explicit, and all
module carriers are the recorded universe `u`. There are no auto-bound variables. The
identity finite morphism reduces to coherence and finite affine sections of F on a locally
Noetherian scheme, as required. No statement dispute was found.

Searches performed:

- `msearch.py leansearch`, query "finite morphism pushforward coherent sheaf locally
  Noetherian finite module sections": service unavailable, Internal Server Error.
- `msearch.py leanfinder`, query "direct image of a coherent module along a finite morphism
  to a locally Noetherian scheme is coherent": eight hits, including `finite_app`,
  `LocallyOfFiniteType.isLocallyNoetherian`, and `SheafOfModules.IsFiniteType`; no exact theorem.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.Scheme.Modules.pushforward`: zero hits.
- `msearch.py grep`, pattern `coherent.*pushforward|pushforward.*coherent` in
  Mathlib/AlgebraicGeometry: two hits in Modules/Tilde, concerning quasi-coherence only.
- `rg` in upstream WeilConjectures and project lean/Sheaf with
  `finite-pushforward-coherent|pushforward.*[Cc]oherent|[Cc]oherent.*pushforward`:
  upstream FinitePushforward provides `isFinitePresentation_pushforward_unit`, only the
  structure-sheaf special case; ClosedImmersion provides only the closed-immersion special
  case. Neither states this node. Project hits are references in proof docstrings.
- Exact-name searches in Mathlib, upstream WeilConjectures, project lean/Sheaf and
  `dag/lean_names_upstream.json` found neither new declaration name already defined.

Validation: server `scompile.py` passes with exit code 0 in 1.8 seconds and no warnings.
The first compile found no monoidal instance for `Y.Modules` with the chosen imports; the
example now uses the existing `SheafOfModules.unit Y.ringCatSheaf` directly, giving the
same structure sheaf without a monoidal-category import.

## Second reading by C1

I independently opened the node, the delivered module, all four statement-dependency
nodes and their recorded declaration sources. No mathematical mismatch was found; the
Lean and node record are retained verbatim. This reading adds only this review report.

The node's objects, hypotheses and conclusions, matched in order:

1. Two schemes and their morphism: `{X Y : Scheme.{u}} (f : Y ⟶ X)` introduces precisely
   the source Y, target X and map of the node. Verdict: exact.
2. Finite f: `[IsFinite f]` uses the recorded Mathlib class, which extends `IsAffineHom f`
   and requires `(f.app U).hom.Finite` for each affine open U. It supplies affine preimages
   and finite coordinate algebras without an additional assumption. Verdict: exact.
3. Locally Noetherian X: `[IsLocallyNoetherian X]` uses the recorded every-affine-open
   definition; its existing affine-cover equivalences match pqf-def-locnoeth. There is
   no separate Noetherian, quasi-compact or nonempty assumption on either scheme.
   Verdict: exact.
4. A coherent O_Y-module: `(F : Y.Modules)` and
   `(hF : RingedSpace.IsCoherent Y.toRingedSpace F)`. I read `Scheme.Modules`, the
   definition of `moduleRings`, and `Coherent.lean`: the carriers agree, and coherence
   means finite type and finite-type kernels of every map from a finite free module
   over every open. No stronger finite-presentation or quasi-coherence binder is added.
   Verdict: exact.
5. Coherence of the O_X-direct image:
   `RingedSpace.IsCoherent X.toRingedSpace ((pushforward f).obj F)` is the first conjunct.
   I read TensorPullback's recorded adjunction to `pushforward g`, and Mathlib's
   `Scheme.Modules.pushforward`, defined using `f.toRingCatSheafHom`. This is the
   recorded module direct image, not an abelian-sheaf image or a private functor.
   Verdict: exact.
6. Every affine U = Spec R, with affine inverse image Spec B:
   `∀ (U : X.Opens), IsAffineOpen U → ...` covers every affine open, using its canonical
   ring `Γ(X, U)` rather than choosing a presentation. Finiteness already supplies
   the preimage's affineness; choosing any Spec R presentation transports the assertion
   along the coordinate-ring isomorphism. Verdict: exact, with no lost presentation.
7. The section equality:
   `Γ((pushforward f).obj F, U) = Γ(F, f ⁻¹ᵁ U)` agrees verbatim with Mathlib's
   `pushforward_obj_obj` signature. Equality is of the existing underlying abelian
   section objects, whose ring action is supplied by the pushforward. Verdict: exact.
8. These sections are finite over R:
   `Module.Finite Γ(X, U) Γ((pushforward f).obj F, U)`. I checked the section-module
   instance in Modules/Sheaf.lean and the presheaf pushforward construction's
   `pushforward₀ F R ⋙ restrictScalars φ`: the action is restriction through f.app U,
   not an arbitrary instance on the section carrier. Verdict: exact.
9. The parenthetical example F = O_Y is supported by the companion
   `isCoherent_unit_of_finite_to_locallyNoetherian`, with the same f, finite and
   locally Noetherian binders, concluding coherence of `SheafOfModules.unit Y.ringCatSheaf`.
   This is the actual structure-sheaf module. Together with the main theorem it gives
   both conclusions for that example. Verdict: exact.
10. The higher-direct-image clause is expressly outside the node's statement, and the
    module has no higher-direct-image assertion. Verdict: exact scope.

Source reading: the repository has no Stacks .tex checkout. I fetched the official
Stacks `coherent.tex` into this item's scratchpad and read lines 2213-2265 and 2452-2480,
including the section's standing locally Noetherian convention, the statement and proof
of lemma-coherent-Noetherian (01XZ), and lemma-finite-pushforward-coherent (01Y6).
The public [01Y6](https://stacks.math.columbia.edu/tag/01Y6) and
[01XZ](https://stacks.math.columbia.edu/tag/01XZ) pages agree. Source and target letters
are exchanged consistently. The source's quasi-coherence assumption follows from the
node's coherence assumption; the source also explicitly derives local Noetherianity
of the source from finiteness over the locally Noetherian target. Thus neither needs
an additional Lean hypothesis. There is no item statement_change or corrected-statement
section, and no new definition node or dependency module to review.

Edge cases: the zero module, empty source, empty target (when such f exists), and empty
open are all admitted; none of the binders requires nonemptiness or a nonzero ring.
The empty open has the zero section module and is included in the affine quantifier.
No index set, n or characteristic enters this statement; coherence's finite free maps
include n = 0 via `Fin n` in the dependency definition. Schemes and their module sections
use the recorded arbitrary universe u; any two schemes can be placed in a common universe.
There is no independent lower test universe or finite-rank restriction. The identity
finite morphism has the expected specialization.

Independent searches, using different wording from the first reader:

- `msearch.py leanfinder "finite direct image preserves finite presentation of
  quasicoherent modules"`: eight hits, all general finite-presentation or
  quasi-coherent-data declarations; none is this scheme statement.
- `msearch.py loogle '"pushforward", "Finite"'`: zero hits.
- `rg` over pinned Mathlib's AlgebraicGeometry, upstream WeilConjectures, and project
  lean/Sheaf for `coherent.*(pushforward|direct.image)`, the reversed pattern,
  `isFinitePresentation_pushforward`, and `isFiniteType_pushforward`: no exact theorem.
  I opened upstream Modules/FinitePushforward.lean's
  `isFinitePresentation_pushforward_unit`: it only treats O_Y. I opened
  Modules/ClosedImmersion.lean's `isFinitePresentation_pushforward_of_isClosedImmersion`:
  it requires a closed immersion. Neither supplies arbitrary coherent F along finite f.
  I also opened the general-site `SheafOfModules.isFinitePresentation_pushforward` and
  `isFinitePresentation_pushforward_of_isLeftAdjoint`: these require the unit image
  to be the target unit (and further hypotheses), which a general finite morphism
  does not satisfy. They cannot replace this node.
- Exact names searched in Mathlib, upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json: neither delivered declaration already occurs.
  The worker's LeanSearch failure and its other searches remain recorded above.

Conventions and proof documentation: no definitions are introduced, hence no hollow
ones. Both proofs are solely `sorry`; no proof was filled. The module and both
statements cite their Stacks places and this blueprint id. The main docstring carries
all eight node proof steps and their dependency ids; the companion spells out step 8.
Imports are used for finiteness, local Noetherianity and coherence. Namespace, file
location, line widths and explicit universe/binders follow the project conventions.
The node's lean.statement is verbatim the main theorem's signature. No mismatch needed
repair and no definition/dependency hole was found.

Validation of the second reading: `scompile.py` compiled the delivered module in 1.8 s,
exit code 0, with no warnings. A direct text comparison confirmed the node's signature
is verbatim and the Lean lines are at most 100 characters. `deliver2.py --no-push`
printed OK, confirming preflight and server compilation before delivery.
