## Worker report

This delivery states `AlgebraicGeometry.Scheme.Modules.exists_elementary_module_devissage`
in `Sheaf.TraceFormula.ElementaryModuleDevissage`, with its single theorem proof `sorry`.
It also defines the missing predicate `Algebra.IsPurelyTranscendentalExtension` in
`Sheaf.FieldTheory.PurelyTranscendentalExtension`, with real data and no postponed proof.
The item's natural-language statement, proof and proof dependencies are unchanged.
Its statement dependencies gain only the new definition node.

I read the current item, all fourteen original statement-dependency nodes and their bindings,
including the source/docstrings of the module definitions used. The recorded Coherent and
TensorPullback modules are absent in the older checkout; I read their current source using
`scompile.py --source`. Coherent's module documentation explicitly binds quasi-coherent and
finite type to Mathlib's `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
Thus its recorded interface is usable, without requiring coherence or finite presentation of F.
The example CompactObject module/node, worker role, setup, goal, state, tools README, stage-2
brief, stage document and delivery-errors H were read. No repair note exists for this item.
The earlier shared delivery by Q36 was a stage-1 split, with no Lean record, rather than a
stage-2 declaration. The sandbox initially contained only dispatcher brief markers.

The source is Stacks `flat.tex`, Tag 057S, lemma-elementary-devissage, statement and whole
proof. The source for the added definition is `fields.tex`, Tag 030E,
definition-transcendence (1)--(3). Both were read locally.

Every hypothesis and conclusion is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S and a morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)` |
| f locally of finite type | `[LocallyOfFiniteType f]` |
| F an O_X-module, finite type and quasi-coherent | `(F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]` |
| x a point, s=f(x) | `(x : X)` and the explicit term `f x` everywhere |
| X_s the scheme-theoretic fibre | `f.fiber (f x)`, Mathlib's pullback along `S.fromSpecResidueField (f x)` |
| F_s the pullback of F to the fibre | `(tensorPullback (f.fiberι (f x))).obj F` |
| x belongs to Supp(F_s) | `hx : ¬ Subsingleton (...presheaf.stalk (f.asFiber x))` |
| Support is the locus of nonzero stalks | The subtype `{q : f.fiber (f x) \| ¬ Subsingleton (...presheaf.stalk q)}` |
| n=dim_x Supp(F_s) | `∃ n : ℕ, topologicalKrullDimAt (⟨f.asFiber x, hx⟩ : ...) = (n : WithBot ℕ∞) ∧ ...` |
| Four schemes and all diagram arrows | Existential `X' Z' Y' S'`, `g e f' i π h`, with precisely the displayed domains and codomains |
| Pointed étale neighbourhoods | `Etale g ∧ Etale e ∧ g x' = x ∧ e s' = f x` |
| The neighbourhoods induce residue-field isomorphisms | `IsIso (g.residueFieldMap x') ∧ IsIso (e.residueFieldMap s')` |
| f g=e f' | `g ≫ f = f' ≫ e` |
| π is over S' | `i ≫ f' = π ≫ h` |
| All four schemes affine | `IsAffine X' ∧ IsAffine Z' ∧ IsAffine Y' ∧ IsAffine S'` |
| i a closed immersion of finite presentation | `IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i` |
| π finite | `IsFinite π` |
| G a finite-type quasi-coherent module on Z' | `(G : Z'.Modules)` and `G.IsFiniteType ∧ G.IsQuasicoherent` |
| i_* G isomorphic to g* F | `Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F)` |
| h smooth of relative dimension n | `SmoothOfRelativeDimension n h` |
| h has geometrically integral fibres | Mathlib's `GeometricallyIntegral h` |
| The distinguished point z' maps to x' | `i z' = x'` |
| y'=π(z') and h(y')=s' | The term `π z'` and `h (π z') = s'` |
| π^{-1}(y')={z'} | `(π ⁻¹' ({π z'} : Set Y')) = {z'}` |
| κ(y')/κ(s') purely transcendental | The last conjunct, `Algebra.IsPurelyTranscendentalExtension`, for the algebra from `(h.residueFieldMap (π z')).hom.toAlgebra` |

Here `f.asFiber x` is the canonical point of the scheme-theoretic fibre, and
`f.fiberι_asFiber` identifies its image with x. No arbitrary lift of the point or
arbitrary field embedding is introduced. The support convention agrees with the project's
inline support convention (nonzero stalk means failure of `Subsingleton`). The existential n
records the value of the dimension, which is a finite nonnegative integer near a point of
this locally finite type fibre support. There is no extra dimension-finiteness hypothesis.
Since `topologicalKrullDimAt` is the dependency's infimum over open neighbourhoods, this uses
dimension at x, not dimension of the stalk or of its closure.

Finite presentation is spelled out in the form given by its dependency node. Quasi-compactness
and quasi-separatedness are also automatic for a closed immersion, so these conclusion clauses
do not strengthen the assertion. The generic coefficient field in the final conjunct is
`S'.residueField (h (π z'))`: the preceding point equality identifies it with κ(s'). This keeps
the actual map induced by h and avoids an arbitrary algebra structure. The local `letI` is
used only for this algebra structure, with an explicit term, and does not hide geometric data.

Mathlib's `GeometricallyIntegral` means that pullback along every field-valued point is integral;
`GeometricallyIntegral.iff_geometricallyIntegral_fiber` states equivalence with geometric
integrality of each scheme-theoretic fibre. Its test-field universe is Mathlib's scheme
universe, with no new independent smaller universe imposed. All schemes have universe u;
the module category, fibres, residue fields and point support have the corresponding u
universes. The new field-extension predicate has two independent field universes u and v,
and quantifies over subsets of the actual larger field rather than a separately sized index.

Dependency declarations and modules used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
  Affineness is `IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: its documented Mathlib bindings
  `SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent`; `Scheme.Modules`
  comes from `Mathlib.AlgebraicGeometry.Modules.Sheaf`. The unused stronger
  `RingedSpace.IsCoherent` is not imposed.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, `QuasiCompact`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension` (which implies Smooth).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, instantiated
  by the canonical `fiber` and `fiberι` in `Mathlib.AlgebraicGeometry.Fiber`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`;
  the canonical `pushforward` is the functor of `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  the full finite-presentation notion is the conjunction with QuasiCompact and QuasiSeparated.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, used through
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`'s `GeometricallyIntegral`.
- `Sheaf.FieldTheory.PurelyTranscendentalExtension`: the new predicate for the residue extension.
  Its dependencies are the field-extension convention `Algebra` and `AlgebraicIndependent`
  from `Mathlib.RingTheory.AlgebraicIndependent.Defs` (the notion in
  def-kun-transcendence-degree), with `IntermediateField.adjoin` from
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, through the Adjoin import.

The published proof-dependency modules for affine étale lifting, residue-field isomorphisms,
quasi-coherent pullback, finite-type pullback and affine pushforward base change are private
imports, as required by stage 2. The other published Mathlib proof dependencies are already
available through the public imports. The two stage-1 children
`lem-trf-finite-type-sheaf-fp-support` and `lem-trf-etale-finite-smooth-local-structure` have no
Lean records and hence no modules to import yet; their later statement landings can add those
proof imports. Neither is needed to type this statement.

Edge cases checked before writing:

- F=0 and an empty X admit no x satisfying hx, exactly as the inherited node requires.
- A module supported at a closed point of A^1 has n=0, while a nonzero free module has
  one-dimensional fibre support. Dimension is computed on the support in the fibre.
- Nonreduced schemes are allowed; there is no reducedness, noetherianity, separability,
  flatness or finite presentation hypothesis on f or F.
- Non-quasi-compact X and S are allowed, since f is only locally of finite type.
- n=0 is allowed and the trivial residue-field extension is purely transcendental
  using the empty independent set. The predicate does not require a nonempty basis.
- In arbitrary characteristic the canonical residue maps remain the same; no perfection
  assumption is made. A transcendence basis with a nontrivial algebraic extension above
  it does NOT satisfy the new definition: `IntermediateField.adjoin k t = ⊤` is required.
- The geometric-integrality condition tests extension of every fibre's residue field,
  and is not merely ordinary integrality of the total space.

Searches for the item (actually executed through msearch.py):

- LeanFinder: `A finite type quasi coherent module admits elementary etale devissage by a
  finite map to a smooth scheme with geometrically integral fibres`: 8 hits, including
  Algebra.Etale.exists_subalgebra_fg and standard-smooth coordinate-chart lemmas, no match.
- Loogle: `"devissage"`: 0 hits.
- Mathlib grep: `devissage|dévissage`: 0 hits. Direct rg over the upstream WeilConjectures
  and project Sheaf trees found other coefficient/derived dévissage statements, none
  with the 057S geometric and module conclusion. The exact node-id search found no module.

No STATEMENT-DISPUTED issue or statement correction is needed. Every universe and variable
is explicit (`autoImplicit false`). No theorem was proved in this stage.

## New nodes

`def-trf-purely-transcendental-extension` defines the field-extension predicate needed by the
last residue-field clause. It is the generating-independent-subset form of Stacks 030E (3).
The equivalence with a rational function field follows from Mathlib's existing
`AlgebraicIndependent.aevalEquivField`: evaluation identifies the fraction field of the
polynomial ring with the field generated by the independent subset. This definition does not
merely assert that the larger field is algebraic over the generated field.

Before creating it I searched all DAG definition nodes for purely/pure transcendental and
found none. The existing field-extension and transcendence-degree nodes do not define this
predicate. `tools/blueprint_refs.py search purely transcendental` returned 0 blueprint nodes;
its ancestor command returned `lem-trf-local-term-locality`. The via ancestry is the item's
ancestry with the item prepended. Direct rg of upstream and project sources found no predicate.
The msearch.py calls and actual results are recorded in the new node and searches.jsonl:

- LeanSearch: `A purely transcendental field extension is generated as a field by an
  algebraically independent subset`: 8 hits concerning transcendence bases and algebraicity,
  without a pure-transcendence predicate.
- Loogle: `AlgebraicIndependent, IntermediateField.adjoin`: 10 hits, including
  AlgebraicIndependent.aevalEquivField and Algebra.FormallySmooth.of_algebraicIndependent.
  These supply the equivalent interpretation and properties, but do not name the predicate.
- Mathlib grep: `PurelyTranscendental|purelyTranscendental|purely transcendental`: 2 hits,
  comments in AlgebraicClosure and Smooth/Field; no existing definition.

The definition's field instances and Algebra instance are the field extension. The existential
`t : Set K` supplies generators, AlgebraicIndependent is the first condition, and equality
of their intermediate-field adjoin with top is the second. The empty and infinitely indexed
cases and unequal field universes are included. It contains no `sorry` and no choice.

## Validation

Both delivered files compiled cleanly through scompile.py in dependency order. This included
the preliminary sibling overlay and the separate final library-path compile of each file.
The full delivery dry run and final delivery are run after this report is written.
The maintainer's independent review is the review for this direct worker delivery.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
