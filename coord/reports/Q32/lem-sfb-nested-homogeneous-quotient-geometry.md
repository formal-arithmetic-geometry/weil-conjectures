## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NestedHomogeneousQuotientGeometry`
states the entire node in two named theorems, both with `sorry`. It defines no new
notion and chooses no quotient scheme. There are no new nodes, dependency repairs,
or statement corrections. Source read: Milne, Algebraic Groups (2017), Proposition
7.15 and Remark 7.16(a),(b), printed pp.142–143, including the Cartesian square and
the reversed arrow in the proposition's second sentence. The DAG already corrects
that arrow. The identity-component source and declaration were also read in full.

The interface uses arbitrary quotient presentations with exactly the conjunction
returned by the recorded `exists_homogeneousQuotient`. This spells out the meaning
of the quotients in the statement, rather than adding conditions on the subgroups.
The all-test-scheme coset criterion and fpqc local lifts identify the represented
coset sheaf, including infinitesimal sections. The flat surjective finitely presented
quotient maps are the maps supplied by that dependency. No normality is assumed.

Hypotheses and clauses, in order:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- `G H J : Over (Spec (.of k))` with `GrpObj` structures are the three group schemes.
  `[IsAffine G.left]`, `[Smooth G.hom]`, `[ConnectedSpace G.left]` give exactly the
  ambient affine smooth connected hypotheses. `[LocallyOfFiniteType G.hom]` and
  `[QuasiCompact G.hom]` together mean finite type. Neither H nor J has a smoothness,
  connectedness, reducedness, or normality hypothesis.
- `(i : H ⟶ J) (j : J ⟶ G)` with `IsClosedSubgroupScheme` on each encode the nested
  closed subgroups. H's inclusion in G is the composite `i ≫ j`.
- `X Y Z` with `qH qJ r` are G/H, G/J, J/H and their quotient maps. `hX hY hZ`
  reproduce, clause for clause, the separatedness, finite type, flatness,
  surjectivity, finite presentation, coset-fibre equivalence, and fpqc-local-lift
  properties in the recorded quotient theorem. In particular these are not arbitrary
  scheme maps masquerading as quotients.
- `∃ π : X ⟶ Y, qH ≫ π = qJ` gives the morphism and its formula on cosets.
  The following universal clause makes it the unique map with this equation.
  `Flat`, `Surjective`, `LocallyOfFinitePresentation`, `QuasiCompact`, and
  `QuasiSeparated` on `π.left` say faithfully flat and of finite presentation.
- `∃ e : G ⊗ Z ≅ pullback qJ π` is the displayed Cartesian isomorphism, in Over k.
  `⊗` here is the standard cartesian product in Over k, hence G ×_k (J/H).
  `e.hom ≫ pullback.fst qJ π = fst G Z` says it is over G. Its equation after
  `lift g (a ≫ r)` specifies `(g,aH) ↦ (g,gaH)` for every test k-scheme T and all
  T-points g of G and a of J. Because r has fpqc local lifts, these equations
  characterize the whole morphism, including sections not globally represented
  by a J-point. They do not identify only the rational or reduced points.
- For every `g : 𝟙_ (Over (Spec (.of k))) ⟶ G`, the isomorphism
  `Z ≅ pullback π (g ≫ qJ)` is the full fibre scheme over qJ(g). Its equation
  after r, namely `((toUnit J ≫ g) * j) ≫ qH`, fixes the map to be aH ↦ gaH.
  Its second projection is the unique map to the terminal k-scheme.
- `topologicalKrullDim H.left = topologicalKrullDim J.left → IsFinite π.left`
  is exactly the equal-topological-Krull-dimension finiteness assertion.
- The second theorem quantifies an arbitrary closed subgroup `j : J ⟶ G` and a
  quotient presentation `Y,qJ,hY`, with the same ambient hypotheses. It concludes
  the existence of `U : J.left.Opens` whose underlying set equals
  `connectedComponent (GrpObj.onePoint J)` and is closed. Thus U is the clopen
  identity component with its open-subscheme structure, not a different model.
- H is literally `U.toScheme.nilradical.subscheme`, with inclusion the composite
  `U.toScheme.nilradical.subschemeι ≫ U.ι`. The smoothness and connectedness
  conclusions concern this exact scheme; its topological Krull dimension equals
  that of J. The existential `gH` is a group-object structure on this explicit
  scheme, constrained by `IsClosedSubgroupScheme` of the actual inclusion into J.
  Since that inclusion is a monomorphism, this structure is determined uniquely.
- The second theorem supplies G/H as `X,qH` with the same quotient characterization,
  and the unique compatible map π to Y. `IsFinite π.left ∧ Flat π.left ∧
  Surjective π.left` is the final finite faithfully flat assertion. No morphism
  is selected from a bare existence statement, and all definition data remain real.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (splitting characterization, equivalent to roots for nonconstant polynomials).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and the standard
  group structure on Hom into a group object.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsSubgroupScheme`, `IsMonHom`;
  used through the recorded homogeneous-quotient dependency's public import.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (includes nonemptiness);
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from its recorded morphism module for finite type.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient`:
  `AlgebraicGeometry.exists_homogeneousQuotient`; its complete statement and
  proof docstring were read. The three quotient-presentation conjunctions are
  its exact outputs, with the respective subgroup inclusions substituted.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, valued in WithBot ℕ∞.
- `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`:
  `AlgebraicGeometry.locallyAlgebraicGroup_identityComponent`; its complete statement
  and proof docstring supply the actual open and its nilradical subscheme.
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic` supplies `GrpObj.onePoint`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  the morphism-conventions node contributes no separate notion. Faithfully flat
  is the conjunction of the recorded scheme predicates `Flat` and `Surjective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the standard cartesian monoidal structure on Over
  supplies `fst`, `lift`, and `⊗`. These are categorical products of actual schemes.

The declared proof-dependency modules are imported: fpqc coverings and their
base change, identity local dimension, zero-dimensional finite-type schemes,
comparison of local-ring and topological dimension, finite morphism permanence,
flat base change, fpqc descent of finite/flat/locally finitely presented morphisms,
representable descent, qcqs permanence, and the locally Noetherian finite
presentation criterion. `lem-sfb-homogeneous-quotient-krull-dimension` has no Lean
record yet and contributes no import. No unstated proof dependency is used in a
statement or replaced by an extra hypothesis. Both docstrings carry the complete
natural-language proof for their respective clauses, with the node's cited steps.

Edge cases checked before writing:

- H = J: J/H is Spec k, π is the canonical identity under the quotient comparison,
  and both the product and fibre formulas specialize correctly.
- H trivial and J = G: X = G and Y = Spec k; e describes the usual trivial product
  description after base change, with the multiplication representative formula.
- Nonreduced subgroups such as μ_p inside G_m in characteristic p are allowed.
  In particular the equal-dimension conclusion applies to finite nonreduced H,J;
  the fibre is an entire scheme, retaining its nilpotents.
- J need not be connected. In the final clause U is its identity component, with
  the other components omitted only for construction of H, not for computing dim J.
- The empty scheme is not silently admitted as a group: the unit from Spec k
  excludes it. Quotient local lifts and surjectivity retain the required nonemptiness.
- There is no characteristic restriction, dimension coerced to ℕ, or independent
  smaller universe for test schemes. Every test scheme is in Scheme.{u}, as in
  the recorded quotient dependency. Indexing covers use Type u as in that interface.

Searches actually run (msearch logs belong to this item):

- LeanFinder: "Nested algebraic group quotient schemes G/H to G/J faithfully flat
  translated fibres J/H finite equal dimension". Eight hits: PreGaloisCategory
  quotient results, abstract quotient maps and `Flat.isQuotientMap_of_surjective`;
  none states the scheme theorem.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Flat`. Eight hits in
  FlatRank, e.g. rank after pullback, but none concerns nested homogeneous quotients.
- msearch grep: `homogeneous.*quotient|quotient.*homogeneous` in AlgebraicGeometry.
  Two ProjectiveSpectrum structure-sheaf hits, neither relevant.
- LeanSearch: "A homogeneous quotient presentation of a group scheme by a closed
  subgroup represents the fppf coset sheaf". Hits were abstract group quotients
  and representation quotients; none defines a scheme presentation predicate.
- LeanSearch: "A homogeneous quotient presentation is a flat surjective finitely
  presented group scheme map with coset fibres and fpqc local lifts". Hits were
  flat quotient topology, scheme maps into Spec of a ring quotient, and abstract
  quotients; none states the nested theorem.
- LeanFinder: "Homogeneous quotient of a group scheme represented by a scheme with
  coset fibres and local lifts"; and grep
  `[Hh]omogeneous.*[Qq]uotient|[Qq]uotient.*[Pp]resentation`. No existing nested
  statement or named presentation predicate. No predicate is introduced here;
  the dependency's explicit conjunction is used directly instead.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for homogeneousQuotient,
  HomogeneousQuotient, nested quotient, the item id, and presentation predicate
  names. Found the dependency theorem and related Borel/orbit geometry, but not
  the nested result. The Borel quotient geometry's presentation style was read
  as a nearby example. The item-id search found no implementation.
- DAG grep for homogeneous quotients and `tools/blueprint_refs.py search
  'homogeneous quotient'`: the latter returned zero blueprint matches. The DAG
  contains this item and its quotient/dimension dependencies; no new node is needed.

Validation: the complete module compiled through scompile.py in sandbox and final
library locations, with no error or warning. All variables/universes are explicit,
`autoImplicit` is false, and the only proof holes are the two named theorem proofs.

## Second reading by Q32

A separate reread of the node, both theorem signatures and the recorded quotient
and identity-component signatures checked each clause above. This is a second
pass by the assigned worker; the dispatcher forbids additional agents and the
maintainer performs the independent delivery review.

The reread checked the order H → J → G and G/H → G/J, that the base-change product
is over k and its isomorphism over G, that the translation equations use g·j rather
than j·g, and that fibre pullback order matches its first projection to X. It also
checked that the final subgroup is the reduction of the open identity component
of J (rather than the reduction of all of J), with the actual nilradical inclusion,
and that equal dimension uses topologicalKrullDim without dropping infinitesimals.
No semantic mismatch or statement correction was found. Direct imports were added
for the recorded pullback, fpqc and morphism-property APIs before final validation.
