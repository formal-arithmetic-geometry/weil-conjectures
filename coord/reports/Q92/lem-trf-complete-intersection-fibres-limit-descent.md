## Worker report

This repair of returned head `f9873fcad875` retains the original mathematical statement
and removes the reported duplicate predicate. It delivers the two original modules and
a module-interface repair of their existing criterion dependency. The required initial
dry run of the saved packet passed at `ff5eda9786`, but did not detect the reported
independent-head collision. The collision is now repaired as described below. Against current main, the item changes only `lean` and adds the
new definition node to `stmt_deps`; its statement and all six proof steps are unchanged.

`Sheaf.TraceFormula.CompleteIntersectionFibresLimitDescent` states
`AlgebraicGeometry.completeIntersectionFibres_limit_descent`, with the sole theorem proof
`sorry`. It also constructs `canonicalBaseChangeMap` using Mathlib's `pullback.map`.
`Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion` already supplies
`AlgebraicGeometry.IsLocalCompleteIntersectionOver`; the repaired
`Sheaf.TraceFormula.LocalCompleteIntersectionScheme` imports and reuses that declaration
and defines only the missing larger-universe scalar-extension chart helper.

The correspondence of every hypothesis and conclusion clause is:

- A nonempty directed set is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  [Nonempty I]`. Its inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`.
- Every `Sᵢ` is quasi-compact and quasi-separated: `[∀ i, CompactSpace (D.obj i)]`
  and `[∀ i, QuasiSeparatedSpace (D.obj i)]`. These were absent in the returned version.
- Affine transitions are `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]`.
  `c : Cone D` and `hc : IsLimit c` supply the limit `S = c.pt` and its projections.
- The fixed stage is `i₀ : I`. The schemes over this stage are `U₀`, `V₀`, `u₀`, `v₀`.
  Each is qcqs by its `CompactSpace` and `QuasiSeparatedSpace` instances, all four
  restored explicitly. No compactness or quasi-separatedness is imposed on the maps
  beyond what follows from these scheme hypotheses.
- The stage morphism is `g₀`; `h₀ : g₀ ≫ v₀ = u₀` says that it is over the base.
  `[LocallyOfFinitePresentation g₀]` is exactly its local finite presentation.
- For a base arrow `p`, the source and target are `pullback u₀ p` and `pullback v₀ p`.
  `canonicalBaseChangeMap g₀ u₀ v₀ p h₀` is the induced arrow. This is actual canonical
  data, not a freely chosen arrow or a `Nonempty` witness. With `p = c.π.app (op i₀)`
  it gives `g`; `hflat` is precisely `Flat g`.
- Every geometric point is represented by its algebraically closed field
  `Ω : Type (max u v)`, `[Field Ω]`, `[IsAlgClosed Ω]`, underlying target point `y`,
  and unital embedding `φ : κ(y) →+* Ω`. This is the residue-field description in
  `def-weil-geometric-point`, whose same-universe bijection is Mathlib's
  `Scheme.SpecToEquivOfField`. Unlike the returned signature, this representation also
  allows `Ω` larger than the original schemes. No algebraicity or finite-extension
  condition is imposed on `φ`.
- `g.fiber y` is Mathlib's ordinary fibre with its canonical
  `g.fiberToSpecResidueField y`. `IsLocalCompleteIntersectionOverExtension _ (g.fiber y)
  (g.fiberToSpecResidueField y) Ω φ` is exactly the geometric-fibre LCI condition;
  its definition and its equivalence with the original scheme condition are explained
  below. This is `hfib`, for every such point, including empty fibres.
- `∃ i, ∃ hi : i₀ ≤ i` gives one common stage. `∀ j, ∀ hj : i ≤ j` gives the whole
  directed tail. Its base arrow is `D.map (homOfLE (hi.trans hj)).op`, so `gj` is
  exactly the same canonical base-change construction over `Sⱼ`.
- The conclusion is `Flat gj ∧ LocallyOfFinitePresentation gj ∧ ...`; the last
  conjunct repeats the identical geometric-point and geometric-fibre condition at
  `Vⱼ`. No condition is dropped or replaced by ordinary fibres.

The extension helper uses an affine open cover `∃ (ι : Type u) (U : ι → X.Opens)`,
`(⨆ i, U i) = ⊤`, and `∀ i, IsAffineOpen (U i)`. Cover indices belong to `Type u`,
which contains `X.Opens`; this avoids the old independently small cover universe.
The coordinate algebra comes from the actual structure morphism via `appLE` and
`Scheme.ΓSpecIso`. `∃ hft : Algebra.FiniteType k Γ(X,U i)` followed by the recorded
`Algebra.IsLocalCompleteIntersection` gives exactly the finite-type ring condition.

The extension helper uses `φ.toAlgebra` and exactly the same induced coordinate algebra.
It requires the canonical rings `Ω ⊗[k] Γ(X,U i)` to be finite type LCI over `Ω`.
These are the coordinate rings of the inverse images of the affine cover under
`X ×_k Ω → X` (Stacks 01JR, 01JQ). Such inverse images cover. Conversely, when the
base-changed scheme is LCI, all its affine open coordinate rings are LCI: refine an LCI
cover by principal affine opens and use the local-ring characterization (01UG and 00S9).
Thus one can take the base changes of any affine cover of `X`. This proves the
mathematical equivalence of the chart formulation and the node's scheme formulation,
without assuming a small field or choosing an arbitrary replacement scheme. In the
application, `k = κ(y)`, so the chart spectra are precisely affine opens in
`U ×_V Spec Ω`, with their canonical `Ω`-algebra structures. The construction remains
valid for identity embeddings and arbitrary transcendental field extensions.

Statement dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition` (limit existence and chart plan).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, and `pullback.map`, supplied with scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`, the canonical ordinary fibre used to scalar extend.
- `Sheaf.RingTheory.CompleteIntersectionOverField`: the recorded
  `Algebra.IsGlobalCompleteIntersection` and `Algebra.IsLocalCompleteIntersection`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparatedSpace`, together
  with topological `CompactSpace`, implements the qcqs scheme conventions.
- The existing criterion module supplies `AlgebraicGeometry.IsLocalCompleteIntersectionOver`;
  the helper module now declares only `AlgebraicGeometry.IsLocalCompleteIntersectionOverExtension`.

The already stated proof dependencies are imported: the affine-chart comparison
(`WeilConjectures.AlgebraicGeometry.AffineChartTensorComparison`), ring descent
(`Sheaf.RingTheory.SyntomicRingFilteredColimitDescent`), LCI field change
(`Sheaf.RingTheory.LocalCompleteIntersectionFieldChange`), and Mathlib finite type and
localization at a prime. The missing local upstream comparison source was read with
`scompile.py --source`, which returned its full live signature and proof. The other
proof-only nodes with no usable Lean record remain proof-only obligations. They are not
silently used as extra hypotheses.

Edge cases checked: empty schemes and fibres use an empty affine cover and are admitted;
the zero coordinate ring is allowed by the recorded ring definition; a constant inverse
system and identity base change give the expected same family; identity and arbitrary
residue embeddings are included; all characteristics and non-Noetherian bases remain
allowed. A field in an arbitrary larger universe is allowed by the independent `v` and
`Type (max u v)`; small fields can be raised canonically with `ULift`. No statement
correction or disputed mathematical claim is needed.

Searches retained from the packet and refreshed for the universe repair:

- `msearch.py leanfinder` query "scheme local complete intersection over a field affine
  open cover": only generic affine-cover declarations.
- `msearch.py leansearch` query "scheme locally complete intersection over a field defined
  by finite type affine chart rings": affine/Noetherian/finite-type declarations, no LCI.
- `msearch.py leanfinder` query "Local complete intersection scheme over a field after a
  field extension in a larger universe, using affine tensor product charts": eight smooth
  base-change results, no LCI notion.
- `msearch.py loogle IsLocalCompleteIntersection`: unknown identifier, no match.
- `msearch.py grep 'IsLocalCompleteIntersection|geometric.*[Ff]ib.*[Ee]xtension'
  AlgebraicGeometry`: no Mathlib match.
- `rg` of both extension names in `WeilConjectures`, `lean/Sheaf`, and `dag/nodes`:
  the old search found no existing declaration or definition node at that time. The repair
  search found the subsequently published base predicate in the criterion module and now
  reuses it. The ring definition is imported. Grepping the item id in upstream found nothing.
- `blueprint_refs.py search complete intersection field` returned only
  `def-pur-frame-class`, a convention using the notion, not its definition. DAG text
  search also found the ring definition and statements about scheme LCI, not another
  scheme-level definition. Raw msearch records are copied into the new node.

## Second reading by Q92

I reread the returned diagnostic, the original item and its six proof steps, all modules,
the dependency signatures, and Stacks 0C3L with its descent situation, 01UG, 01UF, 00SJ,
and the affine-base-change description. H3 was correct: the saved signature omitted qcqs
on all stages and on both initial schemes, and used only fields in the schemes' universe.
All six qcqs typeclass binders are now present (two diagram families and four initial-scheme
instances). Both occurrences of the geometric-point condition use `Type (max u v)` with
point/residue-embedding data, and the new helper uses the actual tensor-product chart rings.
The affine-cover universe is also repaired to `Type u`, so it cannot silently exclude large
covers. The conclusion still has one common index before quantifying over every later stage.
The pullback-arrow definition, its base compatibility, and each of the three conclusion
clauses match the node. The old `let` binders in the theorem conclusion have been expanded.

H8 was also correct: the theorem docstring now supplies all six steps, their named
DAG dependencies, the finite affine-cover argument, canonical ring-map comparison,
conversion from geometric to ordinary fibres, common-index selection, explicit tensor
maps and residue-field base change, and final local-to-global argument. This is a worker
self-check; the maintainer supplies the independent review. Both theorem and helper
universes are explicit and `autoImplicit` is disabled. There are no hollow definitions
and the only postponed proof is the named theorem corresponding to the item.

Compilation uses `scompile.py`, one delivered file at a time in dependency order.
The collision repair required converting the imported criterion to a module with
public declarations; its old non-module form was rejected by Lean. All three files
then compiled without warnings. The dry run caught only a missing explicit dependency
citation in the new definition node; that citation was repaired.

## New nodes

`def-trf-local-complete-intersection-scheme-over-field` is the retained new definition node.
It states the affine-cover scheme LCI notion from Stacks 00S9 and 01UG, with its canonical
scalar-extension chart formulation from 01JR/01JQ and 00SJ. It cites the existing scheme,
spectrum, fibre-product, tensor-product, and ring-LCI nodes. The current criterion module provides the base scheme predicate, which is now reused;
only its larger-universe scalar-extension helper is supplied here. Its scalar-extension
helper belongs to the same notion and is recorded in `lean.declarations`; it introduces
no arbitrary map, choice or extra theorem. Its full source citations, actual search
records, and both explicit cover/field universes have been updated in this repair.


## Repair of returned collision

The returned head reported that `Sheaf.TraceFormula.LocalCompleteIntersectionScheme`
redeclared `AlgebraicGeometry.IsLocalCompleteIntersectionOver`, already declared by
`Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion`. I removed the duplicate
definition and added a public import of that existing predicate. The recorded criterion
file was a legacy non-`module` source and therefore could not be imported by a module-form
stage-2 file. Under the dependency-interface repair rule, I delivered a module-form copy
of the criterion with the same declarations and statement, and recorded the old interface
problem in its `lean.note`. The local module now defines only
`IsLocalCompleteIntersectionOverExtension`, reusing the existing predicate. The item
module and all three delivered modules compile cleanly after this repair.


## Dependency modules

`lem-trf-syntomic-geometric-fibres-affine-criterion`: the live source was a legacy
non-`module` file, so importing it from the consumer failed with
`cannot import non-module Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion
from module`. The dependency module retains all three declaration signatures and bodies,
adds the module/public interface and disables auto-implicit variables. Its recorded
`IsLocalCompleteIntersectionOver` is now the only base scheme predicate in this packet.
Its criterion still states the two equivalences, every affine chart flatness/finite
presentation/residue-fibre condition, and all the existing cover clauses unchanged.
No statement, proof plan, or mathematical hypothesis of this dependency node changes.

The second reading for this collision repair compared the existing predicate's full
open-immersion/spectrum-cover signature with the removed affine-open-coordinate
definition: both express exactly the same finite-type LCI affine-cover condition.
Only the existing signature is retained. The extension helper's cover, induced
algebra, tensor rings, empty-cover case, and independent larger field universe are
unchanged. The main theorem signature is byte-identical to the retained packet.

The first collision-repair dry run accepted the dependency-interface repair and reported
only a missing explicit bracket citation for the criterion in the new definition node.
That citation is now present; no mathematical statement or Lean signature changed.


## Retained-packet repair self-check

The returned immutable head `5a92565a1079` failed while the independent reviewer
attempted to apply a dependency-node JSON as a stage-2 fix. As instructed in the
repair brief, I first retained the saved packet and ran `deliver2.py --no-push`.
The current delivery path accepts the dependency-interface repair under section
1(B), compiles all three modules separately, and reports OK at `8637d15040`.
I did not drop the dependency module or restore the duplicate base predicate.

I reread the three modules and their node statements and compared the saved
node copies against current shared main. The item changes only `lean` and adds
the new definition to `stmt_deps`; the criterion dependency changes only `lean`.
The main theorem retains all six qcqs binders, the directed-tail quantifiers,
canonical base-change arrows, and both larger-universe geometric-fibre conditions.
The extension helper uses the actual induced coordinate algebras and tensor rings.
The criterion retains its two equivalences and covering conditions. The sole
new discrepancy found was whitespace in the criterion's `lean.statement`: its
signature was stored on one line. I copied the signature verbatim from its module
without changing any declaration or mathematical statement.
