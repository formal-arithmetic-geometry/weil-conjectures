## Worker report

Stage 2: `Sheaf.AlgebraicGeometry.EquivariantSmoothGaloisModel` states
`AlgebraicGeometry.exists_equivariant_smooth_galois_model`, with `sorry` as its entire
proof. There are no definitions, helper theorems, new nodes, dependency repairs, or
statement corrections. The theorem docstring contains all nine live DAG proof steps
and their dependency names. The source was read directly: ILO Expose X, printed
pp.149–151 (PDF pages 155–157), Lemma 2.2 and 2.3 Step 2 through diagram (2.b).

The previous dispatch's “stale split” concern was a stage distinction: NK's reviewed
PASS is `reviewed` for the stage-1 split, not `reviewed_lean`; the current node has no
Lean record. This packet supplies that missing stage-2 statement without changing
the reviewed natural-language statement or proof.

Hypotheses and conclusions, clause by clause:

- The field is `(e : Type u) [Field e]`. The scheme over it is `B` with structure
  morphism `b`. `[Nonempty B]` is precisely the nonempty assumption. `[IsProper b]`
  includes separatedness, universal closedness and local finite type; universal
  closedness implies quasi-compactness, so this also gives finite type.
- Normality is `hBnormal`: each stalk is an integral domain and integrally closed.
  The finite disjoint integral components are `hBcomponents`, a finite family of
  pairwise disjoint integral open subschemes covering B. Since the cover is finite,
  each member has open complement, hence is also closed. This is exactly a finite
  disjoint union of integral schemes, including components of different dimensions.
- Geometric reducedness is `[GeometricallyReduced b]`, from the recorded geometric
  integrality/reducedness module. No geometric integrality hypothesis is imposed on B.
- The given Cartier support is represented by `(C : B.IdealSheafData)` and
  `hC : C.IsInvertible`, using the recorded effective Cartier ideal definition.
  The conclusion depends on this datum only through its radical after pullback,
  so different multiplicities with the same support make no difference.
- `∃ K, ∃ Field K, ∃ Algebra e K, Module.Finite e K` is the finite extension K/e.
  `G`, its `Group` and `Finite` structures, and `ρ : G →* (K ≃ₐ[e] K)` give
  a finite group acting by e-automorphisms. Finite groups can be represented in
  `Type u`, so no finite group is excluded. Faithfulness is not required.
- `IsPurelyInseparable e (IntermediateField.fixedField ρ.range)` is precisely K^G/e
  purely inseparable. There is no Galois or separability assumption on K/e itself.
- `Y`, `p`, `Smooth p`, `IsHProjective p` are a smooth projective K-scheme with a
  closed immersion into finite projective space. This is the recorded H-projective
  convention, not merely properness or a projective-bundle variant over K.
- `h`, `IsProjectiveBundle h`, `Surjective h` are the required projective-bundle
  projective surjection to B. `h ≫ b = p ≫ Spec.map (algebraMap e K)` pins the
  scalar compatibility, rather than permitting unrelated structure morphisms.
- `a : G →* Aut Y` is the group action on Y. The invariance equation
  `(a g).hom ≫ h = h` also makes the action one by e-scheme automorphisms.
  The semilinear equivariance equation is
  `(a g).hom ≫ p = p ≫ Spec.map (ρ g⁻¹)`; the inverse converts the left action
  on the field to a left scheme action under contravariance of Spec. This matches
  the existing downstream SemilinearSylowGoodComponents interface.
- `∀ y ∈ genericPoints Y, h y ∈ genericPoints B ∧
  (h.residueFieldMap y).hom.Finite` states maximal domination and finite extensions
  at every generic point, not merely one chosen component or a total degree.
- `(C.comap h).radical.IsSmoothStrictNormalCrossingsDivisor p` is exactly the
  reduced inverse image of the Cartier support. The recorded SNC predicate says
  reduced effective Cartier, finite pairwise noncontained integral components,
  scheme-theoretic union, and smooth intersections whose minimal primes have
  height equal to the number of components. In particular the empty subset
  gives Y, and empty intersections impose no height condition.
- `Q : Subgroup G → Scheme`, `q H : Y ⟶ Q H` provide all subgroup quotients,
  including the full quotient at H = top and the trivial subgroup. The existing
  `IsAdmissibleFiniteSchemeQuotient (a.comp H.subtype) (q H)` gives finiteness,
  invariance, orbit quotient topology, ordinary orbit fibres, and the injective
  section map whose image is exactly invariant sections on every open. Its
  affine-admission clause is automatic here: Y is projective over e (finite
  extension of constants followed by a projective map), hence every finite orbit
  lies in an affine open. Thus it introduces no restriction on the model.
- The separate `∃! r : Q H ⟶ T, q H ≫ r = f` clause for every invariant f
  states categorical descent with its uniqueness for every subgroup, hence also G.
- The separate quantification over every algebraically closed field Ω, surjectivity
  on Ω-valued points, and equivalence of equal images with membership in one H-orbit
  express orbit geometric fibres. This is not replaced by ordinary point fibres.
- `d H` and `q H ≫ d H = h` are the canonical descents of the invariant map h.
  Categorical uniqueness determines these maps; they are not arbitrary comparisons.
- The dense open is `U : B.Opens`, `Dense (U : Set B)`, containing every generic
  point. For an open subset in a scheme, meeting an irreducible component implies
  containing its generic point, so this is the “meeting every component” clause.
  The restricted descended map `(d top).resLE U ((d top) ⁻¹ᵁ U) le_rfl` is
  the pullback `(Y/G) ×_B U → U` expressed as its canonical open restriction.
  `IsFinite` and `(topologically IsHomeomorph).universally` give exactly finite
  universal homeomorphism, using the recorded universal-homeomorphism interface.
- No degree condition, prime, characteristic restriction, geometrical connectedness,
  or prescribed dimension is added.

Dependency declarations used (recorded interfaces read with their docstrings):

- Mathlib.Algebra.Algebra.Defs: `Algebra`; Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`,
  `QuasiCompact`; Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsProper`.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: `Surjective`.
- Mathlib.Topology.Irreducible: `irreducibleComponents`; Mathlib.Topology.Sober:
  `IsGenericPoint`, `genericPoints` (closure of the point is an irreducible component).
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`; Mathlib.AlgebraicGeometry.Properties: `IsIntegral`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral (through Reduced):
  `GeometricallyReduced`; Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  `Scheme.IdealSheafData.IsInvertible`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`.
- Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: `IsProjectiveBundle`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `IsFinite`.
- Mathlib.AlgebraicGeometry.Morphisms.Constructors: `topologically`;
  Mathlib.CategoryTheory.MorphismProperty.Limits: `MorphismProperty.universally`.
- Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor:
  `Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`.
- Sheaf.FieldTheory.FieldTower: `FieldExtension.degree` and its documented
  `Module.Finite` / `IsPurelyInseparable` terminology; Mathlib.FieldTheory.Galois.Basic:
  `IntermediateField.fixedField`; PurelyInseparable.Basic: `IsPurelyInseparable`.
- Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient:
  `IsAdmissibleFiniteSchemeQuotient`. Its existing definition node
  `def-per-admissible-finite-scheme-quotient` is added to stmt_deps; no node is copied
  or restated. All original statement dependencies are retained.

All already recorded proof dependency modules are imported privately unless already
publicly needed for the statement. The five stage-1-only prerequisites from NK's split
(component presentation, plurinodal alteration, nodal resolution, common-field induction,
finite-type field quotient) have no recorded Lean declaration and so supply no module
import yet. They are proof prerequisites, not missing notions in this statement.

Edge cases checked: B empty is deliberately excluded by the node. B disconnected is
retained with one simultaneous K and G and a dense open meeting every component.
Zero-dimensional B is permitted, as are components of different dimensions. The empty
Cartier divisor is the unit ideal: radical pullback is the empty divisor, and the SNC
predicate allows zero components with the empty intersection Y smooth. Characteristic
zero makes the fixed field equal e; positive characteristic permits a genuinely
inseparable fixed extension. Both trivial and full subgroups are quantified. No
faithfulness of G on K or Y is imposed. Nonreduced intersections cannot be hidden,
because the SNC predicate requires smooth scheme-theoretic intersections.

Searches actually run:

- msearch.py leanfinder: “Equivariant smooth Galois model of a normal proper scheme
  with strict normal crossings boundary and finite group quotient”. Eight hits,
  including IsGaloisGroup and smooth-chart results; no combined existence assertion.
- msearch.py loogle: “AlgebraicGeometry.Smooth, CategoryTheory.MulAction”. Unavailable
  identifier CategoryTheory.MulAction; zero returned hits, not evidence of absence.
- msearch.py grep: “GaloisModel|galoisModel|Equivariant.*[Aa]lteration”. Zero hits.
- rg on lean/WeilConjectures and lean/Sheaf for the item id and
  `equivariantSmoothGalois|smooth.galois|SmoothGalois`: only the existing parent
  proof docstring referred to this item; no existing statement.
- rg for quotient predicates and invariant sheaves found the existing
  AdmissibleFiniteSchemeQuotient and SemilinearSylowGoodComponents modules; those
  interfaces are reused instead of defining another quotient notion.
- rg for `EquivariantSmoothGaloisModel|exists_equivariant_smooth_galois_model` in
  both source roots found no existing declaration before writing the module.

No STATEMENT-DISPUTED flag: the source and the live node agree on the model before
any Sylow choice. No stage-1 split, unit statement, or reviewed node text is changed.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
