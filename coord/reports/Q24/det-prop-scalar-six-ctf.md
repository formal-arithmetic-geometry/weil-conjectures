## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixCtf` in
`lean/Sheaf/SixFunctors/ScalarSixCtf.lean`. Its sole theorem has proof `by sorry`.
All definitions have actual data. The original statement, proof and proof dependencies
are unchanged. Only `lean` and additions to `stmt_deps` change on the item.
There is no statement dispute or correction, and no dependency-module replacement.
The released repair note is a resolved stage-1 re-split; its preserved assembly proof
is transcribed step by step in the theorem docstring, rather than reopened.

Hypothesis and clause correspondence:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The field and distinct positive
  characteristic are `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ell)]`. This includes every positive characteristic distinct
  from ell; no algebraic closure, finite base field, smoothness or properness is added.
- The standing scheme is `X : Over (Spec (.of k))` with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`.
  Locally finite type plus quasi-compactness means finite type. Noetherianity needed
  by the closure construction is derived in its definition from these hypotheses,
  not imposed as an extra premise on the theorem.
- The coefficient objects are `{Λ Λ' : ScalarSixRing.{u}}`, the existing bundle of
  commutative condensed rings. The arrow `(a : Λ ⟶ Λ')` includes its ring-map data.
  `ha : IsListedScalarCoefficientMap ell a` renders exactly the specified list and
  finite composites. Constructors `finite`, `integral`, `field`, `localization`,
  `algebraicClosure`, `integralFinite`, and `comp` render its respective cases.
  Finite means `[Finite A]`, discrete means `[DiscreteTopology A]`, and admissibility
  means `(ell : A)^n = 0` for some n, as in the published `IsFinitenessCoefficient`
  convention. `Continuous f` on a finite discrete domain is automatic and imposes
  no restriction on its homomorphisms. The separate integral-to-finite continuity
  binder is the source's continuity hypothesis. The `iso` rule only changes ring
  presentations. It allows finite carriers in Type 0 without excluding a finite
  ring represented in a larger universe. There is no flatness binder.
- All coefficient functors use the small pro-etale site, `Sheaf ... Ab.{u+1}` and
  internal module objects. `scalarSixChange a S` is the existing left functor of
  `Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a.hom.hom S)`:
  ordinary, uncompleted derived extension along the actual pulled-back map.
- Clause (1) quantifies over `K : ConstantModelConstructibleFiniteTor Λ.X X.left`.
  Its `.obj` is the original object of the unbounded derived category. Generators
  are `sfbPerfectScalarGenerator Λ X`: an arbitrary scheme S, immersion a, and
  P with `IsLocallyPerfectScalarModel Λ.X S P`, together with a derived isomorphism
  to the actual extension of P. The finite construction is
  `∃ n : ℕ, (((...shiftClosure ℤ).extensionProductIter n).retractClosure K.obj)`.
  `shiftClosure` permits every integer shift and isomorphic replacement;
  `extensionProductIter n` is n successive extensions by distinguished triangles;
  `retractClosure` permits a direct summand. Iterated mixed finite constructions
  have this form: shifts move through triangles, finite extension trees can be
  associated, and extensions of retracts are retracts of extensions (Mathlib
  `extensionProduct_retractClosure_retractClosure_le`). Thus this formulation
  preserves precisely the finite operations in the node; it invokes no infinite
  coproduct or localizing closure.
- The locally perfect condition is defined in the new local-model node. It gives
  `∃ 𝒰 : Scheme.Cover ... S, ∀ j, ∃ C l h, ...`: an arbitrary pro-etale cover and
  per-chart bounded scalar complex. `IsStrictlyGE l` and `IsStrictlyLE h` express
  boundedness of the complex itself. Each term is a `Retract` of
  `Mod.finiteFree (scalarRingObj Λ) n`, exactly finite generation plus projectivity.
  This is the categorical finite-free-splitting form of `Module.Finite` and
  `Module.Projective`, and hence a perfect scalar-ring complex in the sense of
  `DerivedCategory.IsPerfectRingComplex`. A derived isomorphism identifies the
  restriction of P with `Q.obj (sfbScalarModelComplex ... C)`. That existing
  termwise functor is `finiteConstantScalarExtension`, so it tensors the constant
  scalar sheaf with the coefficient sheaf, rather than using arbitrary sheaf entries.
  Neither chart bounds nor scalar complexes are required to agree across charts.
- Clause (2) uses `∀ (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i) (P : ...)`.
  It does not restrict S to a selected stratification or P to a degree-zero module.
  From `IsLocallyPerfectScalarModel Λ.X S P` it concludes local perfectness of
  `(scalarSixChange a S).obj P` over Λ', and separately its extended object's
  `constantModelBoundedConstructible` and `finiteTorAmplitude`, exactly membership
  in the target `Dctf`. S need not come with an independent structure morphism:
  its structure over k is the composite of i with X.hom.
- The closing convention `a_!=i_*u_!` is rendered by
  `sfbLocallyClosedDerivedExtension`: `a.toImage` is the open immersion into the
  scheme-theoretic closure and `a.imageι` is the closed immersion to X. Apply
  `(openImmersionLowerShriek Λ.X a.toImage).mapDerivedCategory` followed by
  `(lowerStar Λ.X a.imageι).rightDerivedFunctor`. The underlying module pushforward
  is exactly the published `mapMod` followed by `Mod.comap condensedPushforwardHom`;
  no abelian pushforward is silently given a different coefficient action. Closed
  pushforward is exact, so its right-derived functor is canonically its termwise
  localization. This chooses no arbitrary extension or comparison witness.
- Clause (3) quantifies over every source `ConstantModelConstructibleFiniteTor`
  object and concludes both bounded constructibility and finite Tor amplitude of
  its actual image under `scalarSixChange`. This is precisely mapping the source
  full subcategory into its target, with no changed ambient category.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, and the standing-setting binders.
  Compactification data are not needed to define locally closed extension through
  the actual closure; the canonical closure factorization is used instead.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; the existing
  `CommMon` bundle from ScalarSixPullback adds commutativity to that same encoding.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`,
  `padicIntegersRingObj`, `padicIntegersCondensedRingToPadicSubfieldCondensedRing`.
  The closure's sections have values in a finite subextension, not all
  norm-continuous maps into the algebraic closure.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `ProEtale.coefficientMap` and its identity, composition and coefficient-square
  laws, used by the existing scalarSixChange implementation.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `constantModelConstructibleFiniteTor_wellDefined`; its public defining module
  supplies `ConstantModelConstructibleFiniteTor`, `constantModelBoundedConstructible`
  and the published `DerivedCategory.finiteTorAmplitude`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`;
  `Mathlib.Algebra.Module.Projective`: `Module.Projective`;
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`. The full signatures/docstrings were read;
  the new predicate expresses their bounded finite-projective model using the
  existing internal scalar module presentation, with finite-free retracts.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarSections`,
  `scalarRingObj`, `scalarConstant`, `scalarCoefficientHom`,
  `finiteConstantScalarExtension`, `finiteConstantLocalModel_iff_exists_cover`.
- `Sheaf.AlgebraicGeometry.PerfectScalarChangeModel`: `sfbScalarModelComplex`
  and `sfbPerfectScalarChangeModel`; the former is reused, not copied.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek`, the canonical module-valued extension by zero;
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `lowerStar` with its actual coefficient-adjunct restriction action.
- `Sheaf.SixFunctors.ScalarSixPullback`: `ScalarSixRing`, `scalarSixChange`,
  `scalarSixPullback`. The definition owner
  `def-sfb-scalar-six-coefficient-interfaces` is added to stmt_deps; the theorem
  owner stays a proof dependency. No choices of its existential coherence data
  enter the new definitions.
- `Sheaf.SixFunctors.CommonFieldLatticeGenerators`: `latticeIntegralRing`,
  `latticeClosureRing`, `latticeIntegralMap`. These are concrete integral/closure
  coefficient constructions, already listed under that node's lean.declarations.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`:
  `PadicAlgCl.FiniteIntermediateField`, `Profinite.padicSubfieldRingObjMap`,
  `Profinite.padicSubfieldRingObjToPadicAlgCl`.
- Mathlib `ObjectProperty.shiftClosure`, `extensionProductIter`, `retractClosure`
  are the existing finite-construction operations; no duplicate closure is defined.

The main module imports recorded proof-dependency modules as plain imports, and
statement dependencies publicly (directly or through their owning sibling modules).
`lem-weil-pbc-finite-type-over-noetherian` is a Mathlib leaf; its canonical
`LocallyOfFiniteType.isLocallyNoetherian` and quasi-compactness implications are used.
The newly split proof-only nodes `lem-sfb-admissible-scalar-model-cohomology`,
`lem-sfb-stratum-perfect-uniform-bounds`, and `lem-sfb-finite-ctf-retract-etale-images`
have no recorded Lean modules at reading time and are therefore listed in the
proof docstring without invented imports. They are not needed to state the theorem.

Edge cases checked before writing and again after compilation: the empty scheme and
empty pro-etale cover; rank zero, zero ring and zero scalar complex; zero or acyclic
P; identity inclusions E=F (including E=Q_l); arbitrary integers and variable chart
bounds; finite nonflat coefficient homomorphisms; continuous integral-to-finite maps;
and arbitrary nonempty finite chains of listed maps. The zero generator is available
through the zero scalar complex; Mathlib iteration index n=0 means one generator,
so it excludes no zero object. Finite rings in any size are covered up to isomorphism.
No site/coefficient universe equality beyond the project's standard pro-etale
size convention has been imposed.

Searches performed with `msearch.py Q24 det-prop-scalar-six-ctf`:

- LeanFinder: “Extension of scalars preserves bounded constructible complexes of
  finite Tor amplitude generated by locally perfect extension by zero”: 8 hits,
  exact-functor/derived-bounds lemmas and flat ordinary module extension; none is
  this three-clause theorem or either missing predicate.
- Loogle: `ObjectProperty.triangulatedClosure, ObjectProperty.retractClosure`:
  0 hits, unknown identifier ObjectProperty.triangulatedClosure. Reading Mathlib
  instead found the precise shiftClosure/extensionProductIter/retractClosure API.
- LeanSearch: “locally perfect scalar constant sheaf bounded projective complex”:
  8 hits, constant-sheaf characterization and discrete condensed functors;
  no existential bounded scalar-model predicate.
- LeanFinder: “admissible l adic coefficient ring maps finite rings rings of
  integers field inclusion composition”: 8 hits about adele/adic ring maps;
  no listed-map class. LeanSearch “finite admissible l adic coefficient maps
  composite”: 8 adic-completion composition lemmas, no such class.
- Mathlib grep `locallyPerfect|LocallyPerfect|scalar.*constructible`: 0 hits;
  `admissible.*coefficient|coefficient.*admissible` in CategoryTheory: 0 hits.
- Source `rg` in lean/WeilConjectures and lean/Sheaf for local perfectness, scalar
  constructibility, admissible maps and the proposed names: finite discrete
  site-perfectness and dg-ringed-space perfectness have different inputs; existing
  scalar-model construction and scalar-six interfaces are reused as above. No
  exact theorem, local scalar-model predicate or listed-map predicate was found.
  Searching the item id in lean/WeilConjectures gave no hit.
- DAG `rg -l` for locally perfect and listed/coefficient-map phrases, plus
  `blueprint_refs.py search 'locally perfect'`, `'locally perfect scalar'`,
  `'listed coefficient'`, `'listed scalar'`, `'listed scalar coefficient'`:
  only the current blueprint item's locally perfect phrase matched the broad
  query; no existing definition node gives the two missing predicates.
- `blueprint_refs.py ancestor det-prop-scalar-six-ctf` reports the item itself
  as the blueprint.from.node for new nodes. Both new nodes record that ancestry.
- The illustrative CompactObject module has been withdrawn in the read clone;
  its node points to the live Mathlib compact-object interface. The required
  module/public-import/expose header conventions were followed.
- Used `scompile.py --source Sheaf.Paper.CoefficientHeartStratificationDefs` for
  an imported source absent from this local checkout; this was an exploratory
  source read and no copy or replacement of that dependency was introduced.

Validation: scompile.py compiled all three delivered modules separately in dependency
order with no errors or non-sorry warnings. The final main-module run took 32.7 s
for its sandbox check and 11.0 s for its library-name check; the two definition
modules took 7.4 s and 14.7 s for their library-name checks. No direct Lean/lake
command, global build, source-repository write or Git command was used.

## New nodes

`def-sfb-locally-perfect-scalar-model` defines exactly the existential chart-wise
bounded finite-projective scalar model in clause (1), reusing the actual scalar
ring and constant-sheaf extension of the recorded local-model dependency and the
existing `sfbScalarModelComplex`. Source: current scalar-six-ctf clause (1).
The searches above distinguish it from finite discrete site-perfectness, stage-specific
completed perfectness and dg-space perfectness. Its module is
`Sheaf.SixFunctors.LocallyPerfectScalarModel`; no theorem is added there.

`def-sfb-listed-scalar-coefficient-maps` defines the source's complete list of
primitive coefficient maps and finite composites as an inductive predicate on
existing bundled commutative condensed ring morphisms. Source: current scalar-six
unit's coefficient list (1)--(4). Its small helpers only bundle published
continuous-function rings and maps and integral-to-field localization. The integral
and closure maps themselves use the already recorded lattice and finite-subextension
constructions. The searches above found those individual constructions but no class
of listed maps, so the predicate is new. Its module is
`Sheaf.SixFunctors.ListedScalarCoefficientMaps`; no theorem is added there.

Both new nodes use import_flags [unreachable], matching the assigned item's existing
unreachable flag. The item directly cites both new nodes and the already landed
scalar-six coefficient interface definition. No existing dependency node is edited.

## Second reading by Q24

Performed a separate second pass over the item JSON, both new definition nodes, and
all three final module texts in this dispatcher session. No independent sub-agent
was started, as the assignment explicitly prohibits other agents; the maintainer's
independent review remains the delivery review.

Rechecked the actual coefficient endpoints and map constructors, not only their names:
finite discrete maps include nonflat maps; E≤F gives the specified inclusion of
finite subfields and their integer rings; localization and finite-valued closure
are separate constructors; integralFinite retains its specified continuous map;
comp is binary finite composition and iso only changes presentations. Bounds in
the scalar-model predicate are per cover member, not a new global bound. Every
scalar term is a finite-free retract, including rank zero. The derived chart
isomorphism uses the canonical constant-sheaf scalar extension.

Compared each theorem conjunct against the three numbered clauses: the first is
finite shifts/extensions/summands of precisely the locally perfect a_! generators;
the second quantifies over every immersion and every derived P and has both
local-perfectness and target Dctf membership; the third has all source Dctf objects
and both components of target Dctf membership. Verified that a_! really uses
closure-open extension followed by the module pushforward with its coefficient
action. The initial compiler failure was the absence of a synthesized
IsNoetherian X.left, not a missing mathematical hypothesis. The final construction
derives that instance from the original finite-type and quasi-compact binders;
no theorem premise was added. No statement mismatch remained after this repair.
