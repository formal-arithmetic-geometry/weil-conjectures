## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation` states
`AlgebraicGeometry.exists_equivariant_flat_curve_preparation`, with one `sorry` theorem and no
new definitions. The reviewed stage-1 statement, proof and dependencies are unchanged.
NC's delivery on 2026-10-22 was a stage-1 split, not an existing Lean statement; this delivery
uses that split rather than resplitting it. There was no preserved Lean module in the sandbox.
No maintenance repair note for this item was present.

Source checked: de Jong, *Families of curves and alterations* (1997), Sections 2.7--2.10,
printed pp. 603--605, publisher PDF https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf.
Section 2.7 makes the inseparable extension invariant under the finite group. Section 2.9
spreads the generic normalization; Section 2.10 uses equivariant Chow and flattening. The
marking clause follows the node's additionally cited ILO X Theorem 3.4 Step 2 preparation.
The full reviewed thirteen-step DAG proof is in the theorem docstring, including all named
black boxes and the marking's restriction-kernel construction.

Hypotheses, clause by clause:

- A field k: `(k : Type u) [Field k]`.
- Y is normal, projective, geometrically integral and finite type over k:
  `pY : Y ⟶ Spec (.of k)`, `[IsIntegral Y]`, `[IsHProjective pY]`,
  `[GeometricallyIntegral pY]`, and `hnormal`, which requires domain and integrally closed
  local rings at every point. H-projectivity already entails properness, hence finite type;
  no extra finite-type restriction is needed.
- C integral finite type over k: `[IsIntegral C]`, `pC`, `[LocallyOfFiniteType pC]` and
  `[QuasiCompact pC]`. The latter two together are finite type, including global compactness.
- Proper dominant k-morphism g: `(g : C ⟶ Y) [IsProper g] [IsDominant g]` and
  `hg : g ≫ pY = pC`.
- Geometrically integral generic fibre of dimension one:
  `[GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint Y))]` and `hdim`.
- Finite group and compatible actions on k, C, Y: `H : Type v`, `[Group H] [Finite H]`,
  `σk`, `σC`, `σY` are monoid homomorphisms into field/scheme automorphisms. `hC` and `hY`
  specify semilinearity; inverses in `σk h⁻¹` account for the contravariance of Spec and make
  these genuine left actions. `heq` states equivariance of g. No faithfulness is assumed.
- Nowhere dense closed invariant E: `E : Closeds C`, `hE` and `hEstable`.

Conclusions, clause by clause:

- The existential `hgη` and algebra structure identify K→F with the actual transported
  generic-stalk map of g, by an equality of ring homomorphisms. These are output data and
  impose no additional input hypothesis.
- S is normal integral projective finite type over k: existential S, `IsIntegral S`,
  structure map `pS`, `IsHProjective pS` and the local normality conjunction.
- P integral finite type over k: existential P, `IsIntegral P`, and
  `LocallyOfFiniteType (f ≫ pS) ∧ QuasiCompact (f ≫ pS)`.
- Maps b, a, f: the three explicit composition equations state that b and a are k-morphisms
  and `ga=bf`. The k-structure of P is the composite `f ≫ pS`.
- Compatible H-actions are `τS` and `τP`. The four universal equations specify semilinearity
  over k, equivariance of f, b and a; semilinearity of P over k follows by composition.
- H-projective alterations b and a: each has `IsHProjective`, `IsProper`, `Surjective` and
  `IsDominant`, and an existential dense open with `IsFinite` of the restriction. These are
  exactly alterations as defined in the item. The explicit dominance repeats an implication
  of surjectivity so that the generic maps and intended field inclusions are unambiguous.
- f is H-projective, flat and finitely presented: `IsHProjective f`, `Flat f`,
  `LocallyOfFinitePresentation f`. The global quasi-compactness and quasi-separatedness in
  finite presentation follow from H-projectivity (properness); merely locally finite
  presentation on an arbitrary morphism would not have sufficed.
- Pure one-dimensional geometric fibres: for every algebraically closed field Ω and every
  geometric point `s : Spec (.of Ω) ⟶ S`, each irreducible component of `pullback f s` has
  `topologicalKrullDim` equal to one. This is the definition, not an arithmetic-fibre shortcut.
  Nonemptiness also follows from the nonempty generic curve and properness over integral S.
- K0/K finite purely inseparable: the existential `hbη` and algebra structure are tied to
  b's actual generic-stalk map, followed by `Module.Finite` and `IsPurelyInseparable`.
- Pη is the generic fibre over K0: `Pη`, j, q and
  `IsPullback j q f (S.fromSpecStalk (genericPoint S))`. The generic stalk is literally
  `S.functionField`, avoiding a silent identification with a different residue-field type.
- Smooth geometrically integral generic curve: `Smooth q ∧ GeometricallyIntegral q`.
- Normalization of the reduced base-changed original curve: an isomorphism from Pη to
  `(pullback g (S.fromSpecStalk (genericPoint S) ≫ b)).reducedNormalization` with both projection
  equations. The recorded componentwise reduced normalization equals normalization of the
  reduction here, because geometric integrality ensures that the base change is integral.
  The equations specify this over C and over Spec K0, not only as an abstract isomorphism.
- Its function field is F⊗K K0: an existential ring equivalence from the actual tensor
  product to `Pη.functionField`, characterized on every pure tensor. The C-field algebra is
  exactly the generic-stalk map of `j ≫ a`; the K0-algebra is exactly the pullback on global
  sections along q followed by the generic germ. Thus both tensor factors have their required
  maps. The ring equivalence to a field also asserts that the tensor product is a field.
- Reduced inverse image of E: `d : Dη ⟶ Pη` is a closed immersion, `IsReduced Dη`, and
  `Set.range d = (j ≫ a) ⁻¹' E`. A reduced closed subscheme is determined by its closed
  support, so this is precisely the reduced induced closed structure, not a free marking.
- Schematic closure M: `i : M ⟶ P`, `IsClosedImmersion i` and
  `i.ker = (d ≫ j).ker`. `Scheme.Hom.ker` is the ideal defined by restriction on functions.
- H-stability: every `τP h` sends `Set.range i` onto itself. The schematic closure of a
  reduced subscheme is reduced, so stability of this support also specifies its closed
  subscheme structure, with the restricted H-action.
- Finite flat finitely presented M/S: `IsFinite (i ≫ f)`, `Flat (i ≫ f)` and
  `LocallyOfFinitePresentation (i ≫ f)`. Finiteness supplies the missing global conditions.
- Mη finite etale: `Etale ((i ≫ f).fiberToSpecResidueField (genericPoint S))`; its finiteness
  is base change of the explicitly supplied finite morphism M/S. This residue-field fibre
  is canonically the same generic fibre as the generic-stalk version above.
- Empty marking: no nonempty assumption on E, Dη or M; an empty Dη has restriction kernel
  equal to the unit ideal, forcing M empty. No existential positive cardinality is used.

Dependency declarations used (full recorded declaration/source read):

- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionFieldOfComponents`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-pc-field-tower`: `Sheaf.FieldTheory.FieldTower`, `FieldExtension.degree`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-geometric-fibre`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`, `AlgebraicGeometry.Scheme.reducedNormalization`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`.

For the function-field dependency, its module explicitly directs integral-scheme consumers to
Mathlib `Scheme.functionField` (the generic stalk); its general product-of-components
construction is not an arbitrary field extension. The field-tower module also explicitly
records `Module.Finite` and `IsPurelyInseparable` as the existing notions used here.
The completion and formal-power-series dependency nodes only describe proof vocabulary;
they introduce no object or condition in this theorem, so those modules are not gratuitously
imported. Recorded statement-dependency modules used by the signature are public imports;
recorded proof-dependency modules are ordinary imports (deduplicated). The newly split
semilinear Chow prerequisite has no recorded Lean declaration and is left as a stage-3 proof
input, rather than stated here or required as a hypothesis.

Edge cases checked:

- Empty E, trivial H and nonfaithful actions are all admitted, with no extra binder.
- Characteristic zero: a finite purely inseparable inclusion is an isomorphism; no spurious
  positive-characteristic hypothesis is imposed. Characteristic p allows any finite exponent.
- A zero-dimensional projective base is allowed; the generic-stalk pullback still describes
  the entire curve over its field. A singular generic curve is allowed on input and is
  normalized on output; no smoothness is assumed initially.
- Empty C or Y are excluded exactly by integrality. Empty marking is permitted even though
  the generic curve itself is nonempty and one-dimensional.
- H has its own universe v. Geometric test fields lie in the scheme universe u, matching
  Mathlib's geometric definitions, with no independent smaller universe that could make
  the quantification vacuous. All variables and universes are explicit; autoImplicit=false.

Searches for an existing statement:

- `msearch.py ... leansearch` query: "A finite group equivariant flat projective curve
  preparation with purely inseparable base field extension and finite flat marked closure".
  Eight hits: `IsPurelyInseparable`, its field-theory characterizations and trivial/separable
  closure instances, plus `IsGalois.of_fixed_field`. These concern field extensions alone;
  none constructs or states the geometric preparation. The purely inseparable definition
  is reused directly.
- `msearch.py ... leanfinder` query: "Equivariant purely inseparable preparation of a proper
  generic curve by a flat projective family with finite flat horizontal marking". Eight
  hits, all Weierstrass reduction/model/base-change results except
  `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`; none constructs this family.
- `msearch.py ... loogle` query: "AlgebraicGeometry.IsHProjective, AlgebraicGeometry.Flat".
  No hits; Loogle does not index the upstream `IsHProjective` name.
- `msearch.py ... grep` query: "equivariant.*flat.*curve|flat.*curve.*preparation" in
  Mathlib/AlgebraicGeometry: no hits.
- `rg` with the same expression and the exact item id in `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: only the downstream
  EquivariantSingleCurveNodalReduction proof docstring names this item, with no matching
  statement. Its nodal-reduction theorem permits auxiliary separable field extensions and
  does not supply this prescribed purely inseparable generic normalization.
- Read `FlatificationHorizontalCurvePair`, `ReducedNormalization`, the projectivity module,
  `FunctionField`, `FieldTower`, and the recorded Mathlib declarations. Flatification takes
  an already smooth projective generic curve and lacks the semilinear actions and purely
  inseparable preparation, so it is a proof input rather than an existing match.

No statement correction, new nodes, dependency repair, or STATEMENT-DISPUTED flag.

Validation: `scompile.py NH lem-sfb-equivariant-flat-curve-preparation` compiled the delivered
module successfully on the live published server library, in sandbox and module modes
(2.7 and 2.9 seconds respectively), with no errors or warnings. The file contains exactly
one theorem with a `sorry` proof, no definitions, no auto-bound variables, no file-local
notation or instances, and no line above 100 characters. The node's Lean signature is copied
verbatim from the final source. Delivery dry run and final push follow this validation.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
