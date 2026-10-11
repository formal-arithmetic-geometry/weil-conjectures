## Worker report

The module defines `Stalk` and the induced `stalkMap`, then states
`AlgebraicGeometry.coherent_local_isomorphism` with a sorry proof. The hypotheses
`[IsLocallyNoetherian X]`, coherent module assumptions `hF` and `hG`, module map
`φ`, and point `x` are explicit. Its four conjuncts render respectively: a zero
stalk implies a zero restriction on an open neighbourhood; injectivity of the stalk
map implies injectivity of every section map on opens contained in a neighbourhood;
surjectivity implies an epimorphic restricted sheaf map; and bijectivity implies an
isomorphism of restricted sheaves. `F.over U` is Mathlib's open restriction and
`SheafOfModules.overFunctor` is used for restricted morphisms.

Dependencies used are `AlgebraicGeometry.IsLocallyNoetherian` (Mathlib),
`AlgebraicGeometry.RingedSpace.IsCoherent` from `Sheaf.AlgebraicGeometry.Coherent`,
`SheafOfModules` (Mathlib), and `TopCat.Presheaf.stalk` with its module structure
(Mathlib `Mathlib.Algebra.Category.ModuleCat.Stalk`).

Edge cases checked: arbitrary universe `u`, empty opens and zero modules are allowed;
no nonemptiness or separation hypotheses are introduced. The locally Noetherian
assumption is retained even though the source proof notes it is unused.

Searches found no existing local-isomorphism declaration: `msearch.py leanfinder`
for “coherent sheaf stalk map neighbourhood”, `loogle` for
`Scheme.Modules.Hom.isIso_iff_isIso_app`, and grep over Mathlib AlgebraicGeometry
and WeilConjectures. Mathlib stalk and sheaf restriction declarations were reused.

## Earlier second reading (a previous round; superseded)

The theorem has the source hypotheses and four implications in the source order.
The stalk is Mathlib's filtered-colimit stalk with its module structure; restriction
uses `F.over U`. The sectionwise injectivity clause quantifies every open `V ≤ U`,
while the last two clauses use categorical epi and iso for the restricted sheaf map,
matching the sheaf formulation. No mismatch was found.

## Second reading by K1

Read the node statement and all five proof steps, the four statement dependency
nodes and their recorded declarations, and Stacks coherent.tex,
`lemma-local-isomorphism` (01Y3), together with modules.tex 01B8, 01B9 and 01C0.
The repository literature directory has no Stacks checkout on this machine;
I read the available Stacks source copies at
`/home/ubuntu/c1-stacks-review/coherent.tex` and `modules.tex`.
The source lemma introduces exactly the objects and hypotheses below; no additional
ambient hypothesis is needed.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Scheme X: `(X : Scheme.{u})`; arbitrary universe u, now explicitly bound.
- Locally Noetherian: `[IsLocallyNoetherian X]`, the dependency's Mathlib class
  (Noetherian.lean), requiring Noetherian sections on affine opens, equivalent
  to the affine-cover formulation. Retained although the proof does not use it.
- O_X-modules F and G: `SheafOfModules (moduleRings X.toLocallyRingedSpace.toRingedSpace)`.
  Read Mathlib's structure and Hom: abelian-group sheaves with sectionwise module
  structures and semilinear restrictions; Hom components are linear.
- Coherence of both modules: `hF`, `hG` using the recorded `RingedSpace.IsCoherent`.
  Read Coherent.lean: finite type and finite-type kernels of maps from finite free
  modules on every open. No quasi-coherence or extra finiteness hypothesis added.
- Module homomorphism G to F and point x: `(φ : G ⟶ F) (x : X)`; correct direction.
- Stalk F_x: `ModuleCat.of (X.presheaf.stalk x) (TopCat.Presheaf.stalk ... F.val.presheaf x)`.
  Read Mathlib ModuleCat/Stalk.lean: this is the abelian-group filtered colimit,
  with the canonical stalk-ring module action. It realizes the stalk dependency.
- Stalk map φ_x: `Scheme.Modules.Hom.stalkLinearMap (X := X) φ x` from upstream
  FlatPullbackStalk.lean. Read its definition and germ formula: it is linear and
  takes a germ to the germ of its image, exactly the map in the node.
- Restriction: `F.over U` and `(SheafOfModules.overFunctor ... U).map φ`.
  Read PushforwardContinuous.lean: restriction to the slice over U; for the
  opens site its objects are precisely opens V ≤ U and its sections are F(V).
- Clause (1): `IsZero` of the stalk implies `∃ U, x ∈ U ∧ IsZero (F.over U)`.
  IsZero in ModuleCat and in module sheaves means vanishing of the module.
- Clause (2): injectivity of the stalk map implies `∃ U, x ∈ U ∧ ∀ V, V ≤ U →`
  injectivity of `φ.val.app (.op V)`. Every subopen is included, as required.
- Clause (3): surjectivity of the stalk map implies `∃ U, x ∈ U ∧ Epi` of the
  restricted map. Categorical epi in module sheaves is sheaf surjectivity,
  allowing locally lifted sections; it does not assert surjectivity on each open.
- Clause (4): bijectivity of the stalk map implies `∃ U, x ∈ U ∧ IsIso` of that
  same restricted module-sheaf morphism. The inverse is a module morphism.
- Quantifiers: X,F,G,coherence,φ,x precede the four implications; each clause
  chooses its own neighbourhood after its respective stalk hypothesis.

Edge cases: the empty scheme is allowed (the assertion is quantified over its
points); zero modules and zero morphisms are allowed. Clause (2) includes V = ∅.
No nonempty index set, positive rank, n > 0, characteristic, field, separation,
or global Noetherian assumption occurs. Coherence uses all n, including zero.
Scheme and section/stalk modules use the arbitrary shared universe u of the
recorded coherence dependency; no unbound universe or auto-implicit variable remains.

Independent searches: `msearch.py leanfinder` with “finite type module vanishes in
 a neighborhood of a point with zero stalk” found ring-localization support/rank
criteria and the zero-germ criterion, not this four-part sheaf lemma.
`msearch.py loogle` with `"stalk", "isIso"` found the all-stalks isomorphism
criteria, not the one-stalk coherent-neighbourhood result.
`msearch.py leansearch` with “coherent sheaf morphism injective at one stalk
injective on a neighbourhood” returned service unavailable (Internal Server
Error), recorded as unavailable, with no negative verdict inferred.
`msearch.py grep` for `coherent_local|finite.type.*stalk|stalk.*neighbou|local_isomorphism`
and independent rg across Mathlib ModuleCat/AlgebraicGeometry, all upstream
WeilConjectures and the project's lean/Sheaf found no duplicate main theorem.
The project's `FiniteTypeSurjectiveNearStalk` is only clause (3), with a finite-type
hypothesis; it does not state this node. Searching definitions of stalk maps also
found the upstream `Scheme.Modules.Hom.stalkLinearMap` and the project's general
ringed-space `moduleStalkFunctor`, whose signatures and implementations I read.

Mismatches repaired: the worker's undocumented `Stalk` and `stalkMap` abbreviations
were redundant wrappers for existing notions (H4/H8); removed them, using the
Mathlib stalk and upstream linear stalk map directly. The short proof docstring
omitted the kernel-germ computation, zero-map argument, gluing, and dependency
citations (H8); expanded it to all five node proof steps. Added the conventional
copyright header and made Scheme.{u} explicit. No mathematical statement change,
new definition node or dependency module was needed. The node's lean.statement is
verbatim the final theorem signature. The single theorem still has only a sorry
proof; no definitions with holes and nothing newly proved. Server scompile passed
with no errors or warnings before the final docstring formatting cleanup.
