## Worker report

`Sheaf.TraceFormula.RelativeCompletionEtaleApproximation` states
`AlgebraicGeometry.relative_completion_etale_approximation`. Its only postponed proof
is this theorem, with `sorry`; its docstring gives the complete nine-step DAG argument
in six grouped paragraphs. Two real helper constructions in the same module give the
formal base map and the closed point needed for the statement. Both have source and
blueprint docstrings and appear in `lean.declarations`.

I read Stacks `more-morphisms.tex`, lemma-relative-map-approximation-pre (Tag 0GDX),
including the statement and proof, and the full DAG statement and proof. The source has
some stronger conclusions; this module states exactly the conclusions requested by this
node, with the specialization of both bases to finite type over the integers.

Hypotheses and notation, clause by clause:

* Schemes and scheme morphisms are `{X S Y T : Scheme.{u}}`, `f : X ⟶ S`, and
  `g : Y ⟶ T`. The two locally finite type hypotheses are `[LocallyOfFiniteType f]`
  and `[LocallyOfFiniteType g]`.
* Finite type over `Spec ℤ` is expressed by the maps `sZ`, `tZ` to
  `Spec (.of (ULift.{u} ℤ))` and both `[LocallyOfFiniteType]` and `[QuasiCompact]`
  for each. The universe lift only places the integers in the scheme universe.
* The source point `s` is eliminated using `x ↦ s`: it is written `f x` throughout.
  Thus no incidence assumption is lost: given the original `s` and `f x = s`,
  substitution gives exactly this signature. The other incidence equality remains
  `(hyt : g y = t)`.
* `A` is literally the stalk `S.presheaf.stalk (f x)` and `Â` is literally
  `AdicCompletion (IsLocalRing.maximalIdeal A) A`. Every completed local ring in the
  statement is the same maximal-ideal-adic construction on its actual scheme stalk.
* `σ` has domain `T.presheaf.stalk t` and codomain `Â`; `[IsLocalHom σ]` is locality.
  `relativeCompletionFormalBaseMap (f x) t σ` is constructed as
  `Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t`, so it is exactly the required
  composite through `Spec 𝒪_{T,t}`. It is not an arbitrary morphism to `T`.
* `Yσ` is the actual `pullback g (relativeCompletionFormalBaseMap (f x) t σ)`.
  The binder `yσ` is a point of that scheme; `hyσ` says its first projection is `y`.
* `relativeCompletionClosedPoint (f x)` is constructed by pulling the zero prime of
  `A/𝔪_A` back along `AdicCompletion.evalOneₐ`. This is `ker(Â → A/𝔪_A)`, the unique
  maximal ideal of the completion of this Noetherian local ring. `hb` says that the
  second projection of `yσ` is this specific point. No extra local-ring instance or
  hypothesis on the completion is imposed.
* `hformal` supplies an actual ring equivalence from the completion at `x` to the
  completion at `yσ`. Its displayed ring-map equality is precisely scalar
  compatibility over `Â`. On the first side, the scalar map is
  `Classical.choose (RingHom.exists_adicCompletion_map_of_local (f.stalkMap x).hom)`.
  Its finite quotient formulas uniquely determine it: every coordinate has a residue
  representative and evaluation detects equality of compatible sequences. This is
  the canonical completion of the stalk map, so the allowed uniqueness-based choice
  does not choose arbitrary data. On the second side, the scalar map is explicitly
  constants `StructureSheaf.toStalk` on `Spec Â`, followed by the pullback projection's
  stalk map, followed by the ordinary map to the completion. Therefore the equality
  says exactly that this ring equivalence is an isomorphism of the canonical
  `Â`-algebras, without arbitrary algebra structures or continuity assumptions.

Conclusion, clause by clause:

* `V,v,a` supply `(V,v) → (S,s)`, with `a v = f x` and `Etale a`.
* `τ : V ⟶ T` and `τ v = t` supply the approximated morphism of bases.
* `U,u,e` supply `(U,u) → (X,x)`, with `e u = x` and `Etale e`.
* `w : U ⟶ V`, `w u = v`, and `w ≫ a = e ≫ f` give the specified point over `v`
  and the triangle over `S`.
* `m : U ⟶ pullback g τ`, `Etale m`, and `m ≫ pullback.snd g τ = w` give the
  étale `V`-morphism to the canonical `Y ×_{T,τ} V` and the triangle over `V`.
* `IsIso (a.residueFieldMap v)` and `IsIso (e.residueFieldMap u)` express
  isomorphisms of the actual induced maps `κ(s) → κ(v)` and `κ(x) → κ(u)`.
* No matching with the original formal equivalence is required in the conclusion.
  No residue isomorphism for `m`, marked image in `Y ×_T V`, singleton fibre, or
  other stronger conclusion from the source is silently added.

Dependency declarations and modules:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, declaration `LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, declaration `QuasiCompact`.
* `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  declaration `AdicCompletion`, with its real ring structure and completion maps
  from `Mathlib.RingTheory.AdicCompletion.Algebra`.
* `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declarations
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.
* `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  declaration `AlgebraicGeometry.Etale`. The recorded old `IsEtale` name is a
  deprecated alias; the current class is `Etale`.
* `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, declarations
  `Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
* Added landed statement dependency `lem-weil-pbc-fs-adic-completion-map-local`:
  `Sheaf.RingTheory.CompletionMapForLocalHom`, declaration
  `RingHom.exists_adicCompletion_map_of_local`. I read its node, full signature,
  proof docstring and implementation. It is used to supply the canonical scalar map,
  not restated or modified. This uses the authorization to add landed dependency nodes.

The module also imports every available recorded proof-dependency module privately.
Five direct proof dependencies have no recorded declaration/module yet:
`lem-trf-completed-local-base-change`, `lem-trf-finite-residue-point-closed-in-fibre`,
`lem-trf-fixed-family-etale-span-descent`, `lem-trf-isomorphism-completion-approximation`,
and `lem-trf-smooth-point-etale-immersion`. They are proof inputs only and do not prevent
this stage-2 statement from being written; no new proof lemma or placeholder is introduced.

Edge cases checked: marked points exclude an empty source or zero stalk locally, but no
global nonemptiness assumption is added. The schemes need not be globally affine or
separated. No closedness of `x`, `s`, `y`, or `t` is assumed; only the projection of
`yσ` to the completed base is the closed point. All characteristics and all common scheme
universes are allowed; the lifted integers do not force a small universe. `σ` may be the
identity or any other local map; it is not required to be an algebra map relative to an
unspecified map `T → S`. The canonical scalar compatibility is essential and retained.
Both residue maps are the induced maps, not arbitrary field equivalences. Identity
families and identity formal isomorphisms satisfy the hypothesis and permit identity
neighbourhoods. The two helper definitions contain actual data and no postponed proofs.

Searches performed using `msearch.py N0 lem-trf-relative-completion-etale-approximation`
(the script records the queries in `searches.jsonl`):

* `leanfinder`, query “Relative Artin approximation for locally finite type schemes with
  an isomorphism of completed local rings over the completed base”: eight hits, on
  locally Artinian schemes, local finite presentation and finite maps; none is relative
  Artin approximation.
* `loogle`, query `"approximation", "Etale"`: zero hits.
* `grep`, query `0GDX|relative.*completion.*approximation|relative.map.approximation`:
  zero Mathlib hits.
* `leansearch`, query “Relative Artin approximation from an isomorphism of completed
  local rings of two locally finite type schemes over finite type integer bases”:
  eight hits on Artinian rings/schemes, Laurent series and finite-type morphisms;
  none states this result.
* `rg` in the source `WeilConjectures/` and project `lean/Sheaf/` for relative completion
  and approximation: only unrelated approximation theorems and the nodal-local-model
  consumer's proof docstring; no theorem matching this node. Exact node-id grep in
  the source finds no declaration.
* The generic completed stalk map already exists in
  `Sheaf.RingTheory.CompletionMapForLocalHom` and the generic coefficient/stalk maps
  exist in Mathlib, so the statement uses them. No duplicate completion construction,
  private copy of a dependency, or independent new notion is introduced.

Validation: `scompile.py` compiled the delivered module separately in sandbox and library
form, including the published side-library overlay, with no errors or non-sorry warnings.
The initial draft was repaired before delivery: arbitrary scalar maps were replaced by
canonical ones, the closed-point side condition by its canonical construction, and all
statement-level `let` bindings were removed. The report describes the final signature.

No statement correction, new node, dependency-record repair, `STATEMENT-DISPUTED`, or
unresolved node fault is needed.

## Second reading by N0

I independently reopened the node, the declaration, and every recorded dependency. The
Lean binders `{X S Y T : Scheme.{u}}`, `f`, `g`, the two `LocallyOfFiniteType` instances,
and the maps `sZ` and `tZ` with their `LocallyOfFiniteType` and `QuasiCompact` instances
render exactly the scheme and finite-type-over-`Spec ℤ` hypotheses. The source points are
represented by `x`, `y`, and `t`, with `f x` serving as the node's `s` after substitution
and `hyt : g y = t` retaining the other incidence equality.

The ring map `σ` has precisely the stated domain `T.presheaf.stalk t`, codomain the
maximal-ideal completion of `S.presheaf.stalk (f x)`, and `[IsLocalHom σ]`. The helper
`relativeCompletionFormalBaseMap` is the canonical composite through `Spec 𝒪_{T,t}`.
The point `yσ` lies in the actual pullback, `hyσ` is its first-projection equality to `y`,
and `hb` identifies the second projection with the constructed closed point. The
`hformal` existential is a ring equivalence between exactly the two completed stalks;
its equation uses the chosen completion of the local stalk map on the source and the
explicit constants, projection stalk map, and completion map on the target. Thus it
expresses the required completed-base algebra compatibility without introducing an
arbitrary scalar map or an extra hypothesis.

The conclusion binds `V,v,a,τ` and `U,u,w,e,m` with the same objects as the node. Each
conjunct is present: `a v = f x`, `τ v = t`, `e u = x`, `w u = v`, the triangle
`w ≫ a = e ≫ f`, the pullback triangle `m ≫ pullback.snd g τ = w`, étaleness of `a`,
`e`, and `m`, and `IsIso` for the two induced residue-field maps. No residue isomorphism
for `m`, formal-map equality, separatedness, closedness of the original points, or other
stronger conclusion appears. The dependency declarations were checked at their recorded
modules and signatures; the completion-map dependency is used only for the canonical
source scalar map. The two helper definitions contain real constructions and the theorem
proof is the sole `sorry`. The module compiled cleanly with `scompile.py`, so this repair
changes only the packet metadata and report reading, not the mathematical statement.

## Second reading by Q48

I independently opened the node statement, its source place (Stacks Tag 0GDX), and the
module signature. The binders `f` and `g` with `LocallyOfFiniteType`, and the two structure
maps `sZ` and `tZ` with both `LocallyOfFiniteType` and `QuasiCompact`, render the two
finite-type-over-`Spec ℤ` hypotheses. The point `s` is represented by `f x`, while `hyt`
retains the required equality `g y = t`. The local map `σ` has exactly the stalk-at-`t`
to maximal-ideal completion-at-`f x` type and its `[IsLocalHom σ]` instance expresses
locality. The helper `relativeCompletionFormalBaseMap` is the specified composite through
`Spec 𝒪_{T,t}`, and `relativeCompletionClosedPoint` is the canonical completion closed
point; hence `yσ`, `hyσ`, and `hb` identify the required point of the canonical pullback.
The `hformal` existential uses a ring equivalence between precisely the two completed
stalks and equates the canonical completed stalk map with the constants/projection map.
In the conclusion, `V,v,a,τ` provide the pointed etale base neighborhood and varying map to
`T`; `U,u,w,e,m` provide the pointed etale neighborhood, its map to `X`, and the etale
`V`-map to `pullback g τ`. The two commuting triangles are exactly `w ≫ a = e ≫ f`
and `m ≫ pullback.snd g τ = w`, and the point equations are all present. The two residue
field clauses are `IsIso (a.residueFieldMap v)` and `IsIso (e.residueFieldMap u)`. No
extra equality with the formal isomorphism, residue condition for `m`, or singleton-fibre
claim appears. The declaration and its helper definitions therefore match every clause of
the node without adding or dropping hypotheses.
