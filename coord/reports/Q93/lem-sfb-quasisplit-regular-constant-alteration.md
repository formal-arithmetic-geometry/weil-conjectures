## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiSplitRegularConstantAlteration` states
`AlgebraicGeometry.exists_quasiSplit_regular_constant_alteration`, with `sorry` as its
only proof. No new definitions, dependency repairs or statement corrections are needed.
The node copy changes only `lean`.

Source read: de Jong, *Families of curves and alterations* (1997), printed pp. 614--615,
Lemmas 5.5 and 5.7 and the quasi-split definition between them; Theorem 5.9 and its
final ordinary fibre-product construction, printed pp. 616--617. The publisher PDF is
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf. The formulation follows the
node's combination of these constructions, rather than identifying it with either
individual lemma. The complete ten-step DAG proof is in the theorem's docstring.

Hypotheses, individually:

- The field is `(k : Type u) [Field k]`. All four schemes have universe `u` and
  `IsIntegral` instances. Structure morphisms are explicitly `pY`, `pC`, `pS`;
  the structure morphism of W is `f ≫ pS`.
- Normality of Y and S is `hYnormal`, `hSnormal`, requiring both `IsDomain` and
  `IsIntegrallyClosed` at every local ring, exactly the node's stated convention.
- Y is projective and geometrically integral over k through `IsHProjective pY`
  and `GeometricallyIntegral pY`. C is proper through `IsProper pC`; S is
  projective through `IsHProjective pS`. Properness implies finite type, so
  these encode all three finite-type conditions without extra assumptions.
- The proper dominant k-morphism g is `(g : C ⟶ Y) [IsProper g]`, `hg` for the
  structure-map identity, and `hgdominant` for preservation of generic points.
  On integral schemes this is precisely dominance.
- The alteration b₀ is `IsProper b₀`, `Surjective b₀`, `hb₀finite`, and
  `Module.Finite Y.functionField S.functionField`. `hb₀` states it is over k.
  `hb₀field` ties the algebra structure to the actual morphism: the square of
  canonical generic spectra commutes. The quantified algebra is therefore no
  additional freedom or hypothesis beyond the specified field extension.
- The H-projective stable pointed curve is `f`, `IsHProjective f`, `n : ℕ`,
  `s : Fin n → (S ⟶ W)`, `hs`, and `hstable : IsStablePointedCurve f s hs`.
  Flatness, finite presentation, nodal geometric fibres, the stability inequalities,
  and disjoint smooth markings are those of the recorded dependency predicate.
- Smooth geometrically integral generic fibre uses `Smooth` and
  `GeometricallyIntegral` on `f.fiberToSpecResidueField (genericPoint S)`.
- The dominant morphism a₀ is `a₀` and `ha₀dominant`; its square is `ha₀`.
  Its finite field extension is the corresponding `Algebra` and `Module.Finite`
  instances; `ha₀field` identifies the inclusion by the generic-spectrum square.
  Together with `hg` and `hb₀`, the square also makes a₀ a k-morphism.
- Finite groups H and J are arbitrary `Type v` and `Type w` with `Group` and
  `Finite`; `β` and `hβ` give the surjection.
- Actions are `σk`, `σY`, `σC`, `σS`, `σW`. The first three are H-actions,
  the last two J-actions. `hY`, `hC`, `hS` give semilinearity over k, using
  inverse elements under contravariant Spec. `hgeq`, `hb₀eq`, `hfeq`, `ha₀eq`
  give equivariance of every arrow through β. Semilinearity of W then follows
  from `hfeq` and `hS`; no separate redundant binder is imposed.
- The J-stable union of markings is `hmark`, as equality of the image of the
  union with itself. It neither fixes labels nor assumes faithfulness.
- A₀ is `β.ker`. K and F are `Y.functionField` and `C.functionField`.
  `hSinsep` and `hWinsep` quantify intermediate fields whose membership is
  exactly being fixed by all kernel elements, and require `IsPurelyInseparable`
  over those canonical base fields. Thus they state precisely the two given
  invariant-field extensions, not just inclusion in some fixed subfield.

Conclusions, individually:

- The finite group G has universe `max u v w`, a `Group` and `Finite` instance;
  `ρ : G →* J` is surjective. This accommodates arbitrary finite input groups.
- S₄ is an integral scheme with local-ring normality and projective structure
  morphism `r ≫ pS`. The map `r` is finite and surjective. Generic etaleness is
  the explicit `∃ U : S.Opens, Dense (U : Set S) ∧ Etale (r ∣_ U)`.
  Its action is `σ₄`; the following equation makes r equivariant through ρ.
  Finite type is implied by H-projectivity.
- The fixed-field equality for S₄ is stated with the actual `Algebra` map,
  identified by its generic-spectrum square: its range consists exactly of
  elements fixed by `ρ.ker`. There is no arbitrary replacement embedding.
- The extension e/k is a field with an `Algebra` and `Module.Finite` structure.
  `γ` is the G-action, with its displayed equation extending `σk` via βρ.
  An intermediate field E characterized by fixedness under `(β.comp ρ).ker`
  has `IsPurelyInseparable k E`, rendering e^A/k.
- B is integral, normal at every local ring, H-projective and geometrically
  integral over e via pB; hence finite type over e. The map q to S₄ is finite,
  surjective and `UniversallyInjective` (radicial), equivariant for τB and σ₄.
  Its structure equation identifies B's k-structure with the given e/k map.
  The τB/pB equation is semilinearity for γ.
- The field extension B/S₄ has its canonical generic-spectrum square and
  `Module.Finite` and `IsPurelyInseparable` conclusions.
- The composite b is literally `q ≫ r ≫ b₀`. Its H-projectivity, properness,
  surjectivity, finiteness over a dense target open and finite canonical
  function-field extension give all clauses of the node's alteration definition.
  Its invariant intermediate field is characterized by `(β.comp ρ).ker`, and
  is purely inseparable over `Y.functionField`. Equivariance is explicit below.
- If `topologicalKrullDim Y = 0`, `IsIso pB` says that the structural map is
  an isomorphism B ≅ Spec e, the invariant meaning of B = Spec e.
- V is exactly `pullback f (q ≫ r)` with an `IsIntegral` instance. Its morphism
  v is exactly `pullback.snd f (q ≫ r)`. The G-action τV commutes with both
  canonical projections, hence is precisely the diagonal action. It cannot
  be an unrelated action on another family.
- H-projectivity, the stable pointed predicate, smooth geometrically integral
  generic fibre and `HasQuasiSplitNodalFibres` are stated for this v. The marked
  sections are exactly `f.baseChangeSection (s i) (hs i) (q ≫ r)` with the
  canonical section identities `Scheme.Hom.baseChangeSection_snd`.
- Disjointness and smoothness of the pulled-back sections are included in the
  same `IsStablePointedCurve` predicate. The following set-image equality
  explicitly gives their G-stable union, allowing permutation of the sections.
- The composite c is literally `pullback.fst f (q ≫ r) ≫ a₀`. H-projectivity,
  properness, surjectivity, finiteness over a dense target open and a finite
  canonical function-field extension make it the asserted alteration. Its
  kernel-fixed intermediate field is purely inseparable over C.functionField.
- The last two equivariance formulas give equivariance of b and c through βρ.
  The final equality is precisely `gc = bv` in Lean composition order.

Dependency interfaces read and used:

- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (finite projective-space embedding).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Sheaf.FieldTheory.FieldTower`: the node's recorded module and its documented
  existing `Module.Finite` and `IsPurelyInseparable` clauses; purely inseparable
  extensions use `Mathlib.FieldTheory.PurelyInseparable.Basic` directly.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, used within the stable predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the integral-scheme clause
  is Mathlib `Scheme.functionField`, the generic stalk (not the product for a
  reducible scheme). `WeilConjectures.AlgebraicGeometry.StalkAut` supplies
  `Scheme.functionFieldAut` for the actual induced automorphisms.
- `Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres`:
  `AlgebraicGeometry.HasQuasiSplitNodalFibres`.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`:
  `AlgebraicGeometry.IsStablePointedCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, inside H-projectivity.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, implied by properness.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, inside
  the recorded stable pointed predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`:
  `AlgebraicGeometry.UniversallyInjective`, for the inline radicial convention.
- `WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection`:
  `Scheme.Hom.baseChangeSection`, `Scheme.Hom.baseChangeSection_snd`, already
  publicly imported by the stable-pointed dependency.

All recorded proof-dependency modules are imported without `public` unless they
are also a statement dependency. In particular this includes the finite
quasi-splitting, constant-regularization, kernel-invariant-tower, stable-extension,
H-projective composition, projective generic-finiteness and semistable-base-change
modules. Dependencies with only Mathlib matches require no new statements.

Edge cases checked before and during writing: n = 0 uses Fin 0 and the empty
union, so no markings are excluded. Trivial groups and nonfaithful actions are
allowed; only the two given quotient homomorphisms are surjective. Characteristic
zero is covered by Mathlib's purely inseparable predicate (then the embeddings
are surjective). Positive characteristic and imperfect fields have no perfectness
assumption. Smooth fibres make the quasi-split condition vacuous, as required.
Self-nodes are retained by the recorded normalization/branch predicate. Dim Y = 0
is explicitly included. Empty schemes are already excluded by the node's integral
hypotheses. C is only proper, not assumed projective over k. No new equality of
independent universes or restriction on group cardinalities is imposed.

Searches actually run:

- msearch LeanFinder: `Equivariant finite quasi splitting of nodal curves and
  radicial regularization of constants`: eight Weierstrass-curve hits, no match.
- msearch Loogle: `AlgebraicGeometry.HasQuasiSplitNodalFibres,
  AlgebraicGeometry.IsStablePointedCurve`: zero hits, unknown first identifier;
  the notions are project definitions, not Mathlib declarations.
- msearch grep: `quasiSplit|quasisplit|regular.*constant` in Mathlib
  AlgebraicGeometry: zero hits.
- msearch LeanSearch: `Finite equivariant alteration of stable curves with quasi
  split fibres and purely inseparable invariant fields`: search output retained
  in the sandbox search log; no exact theorem for this combined construction.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `quasisplit|quasiSplit|constant_regularization|lem-sfb-quasisplit-regular-constant-alteration`:
  only the two separate construction interfaces and the unrelated affine-groupoid
  pointed quasi-splitting module. Read the two construction modules in full.
- rg for the exact node id and new declaration name in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf`: no existing combined declaration.

Validation: prescribed scompile.py server compilation completed successfully for
both its sandbox and final module checks, without errors or warnings. Only the
expected postponed theorem proof is present. Every variable and universe is explicit,
with `set_option autoImplicit false`. The source is in module mode. No live files
were modified and no global build was run.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
