## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixDirectImage`
in `Sheaf.SixFunctors.ScalarSixDirectImage`. Its only postponed proof is that theorem;
it ends with `by sorry`. The separate definition module contains no sorry.
The item's mathematical statement is unchanged. Its stmt_deps gains the new definition
node `def-sfb-listed-coefficient-maps`.

Hypotheses and clauses, checked against the node and the current blueprint:

- Prime ell is `(ell : ℕ) [Fact ell.Prime]`. The standing base is `(k : Type u)
  [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]`, exactly positive
  characteristic different from ell. It does not require an algebraically closed
  or finite field.
- `X Y : Over (Spec (.of k))`, each with `LocallyOfFiniteType`, `QuasiCompact` and
  `IsSeparated` on its structural map, give separated finite-type k-schemes.
  `f : X ⟶ Y` is a k-morphism, with underlying map `f.left`. No additional
  properness, smoothness, finiteness, dimension or cohomological-dimension bound
  is assumed.
- `Λ Λ' : ScalarSixRing.{u}` are the published bundled commutative condensed
  ring objects. `a : Λ ⟶ Λ'` preserves their ring structures.
  `ListedCoefficientMap ell a` selects exactly the six listed families and
  finite composites; its constructors are detailed below.
- `scalarSixChange a Z` is the recorded ordinary uncompleted total left derived
  extension along `coefficientMap a.hom.hom Z`.
- The displayed gamma is literally the existing `(scalarDirectImageMate a f.left).app K`.
  That definition is `mateEquiv` for `RootCoordinateFace.adjunction` and the inverse
  of `scalarDirectImagePullbackData.theta`. Expanding the mate gives eta' at T R K,
  then R' of theta inverse at R K, then R' T of epsilon at K, precisely the node's
  unit / pullback identification / scalar-extended counit composite. Theta is fixed
  by `ScalarSixPullbackData.thetaNormalization = scalarSixPullHom`; it is not an
  arbitrary pullback isomorphism. The choice in the dependency chooses only this
  normalized map and proofs of its laws.
- Clause (1): the first conjunct universally quantifies ambient derived `K`, with
  hypothesis `constantModelBoundedConstructible Λ.X X.left K ∧
  DerivedCategory.finiteTorAmplitude _ K`. This is precisely the recorded Dctf
  condition, using finite constant scalar models. The conclusion gives `IsIso`
  of this specified gamma, followed by the same Dctf predicate for its source
  `(scalarSixChange a Y.left).obj ((RootCoordinateFace.lower Λ.X f.left).obj K)`
  and its target `(RootCoordinateFace.lower Λ'.X f.left).obj
  ((scalarSixChange a X.left).obj K)` separately.
- Clause (2), naturality: the second conjunct quantifies every ambient `K K'`
  and `h : K ⟶ K'` and displays the naturality square for these two composites.
- Clause (2), geometric composition: the third conjunct quantifies a third
  standing scheme W and `g : Y ⟶ W`, and every ambient K. Its equation includes
  `RootCoordinateFace.lowerComp` at both coefficient rings. Moving the target
  compositor to the right gives exactly gamma_gf = Rg'(gamma_f) gamma_g,RfK
  under R(gf) = Rg Rf. The compositor is the conjugate of the exact pullback
  compositor under the same adjunctions, not a chosen unrelated isomorphism.
- Clause (2), unit: the fourth conjunct is
  `T_Y.map eta_N ≫ gamma.app (f^*N) = eta'_(T_Y N) ≫ R'_f.map (theta.inv.app N)`.
  This is the node's unit equation in Lean's left-to-right composition notation.
- Clause (2), counit: the final conjunct is
  `f'^*.map gamma_K ≫ epsilon'_(T_X K) = theta.inv.app (Rf K) ≫ T_X.map epsilon_K`,
  exactly the node's counit equation. Both equations, naturality and composition
  quantify ambient derived objects without Dctf or boundedness assumptions.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` and its standing Over-scheme convention; no
  compactification choice is needed for ordinary direct image.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the public coefficient constructions.
  The maps use finite intermediate fields in the fixed algebraic closure and
  their existing valuation rings, the same coefficient convention.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; `ScalarSixRing`
  is its published commutative bundling in `Sheaf.SixFunctors.ScalarSixPullback`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing` and `padicAlgClRingObj`, whose sections take
  values in one finite subextension; the all-continuous-function algebraic
  closure is never used.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `coefficientMap_id`, `coefficientMap_comp`, coefficient squares.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`
  and the underlying constant-model predicate; finite Tor amplitude uses
  the existing `DerivedCategory.finiteTorAmplitude`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction`. For the exact inverse-image presentation,
  `RootCoordinateFace.adjunction` is the existing localization adjunction from
  that same ordinary module adjunction; `RootCoordinateFace.lower` is the
  recorded `moduleObjectDerivedPushforward`, literally the total right derived
  functor. No replacement adjunction is introduced.
- `Sheaf.SixFunctors.ScalarSixPullback`: `scalarSixChange`, `scalarSixPull`,
  `scalarSixPullHom`, `ScalarSixPullbackData`, `scalarSixPullback`.
- `Sheaf.SixFunctors.ScalarDirectImageMateCoherence`:
  `scalarDirectImagePullbackData`, `scalarDirectImageMate`,
  `scalarDirectImageMateCoherence`, and its public `RootCoordinateFace` interface.
- `Sheaf.Paper.CartesianCoefficients` and its public finite-free module:
  `cartesianFinitePointRing`, `finiteCoefficientIntegersPointMap`;
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`:
  `Profinite.padicSubfieldRingObjMap`, `padicSubfieldRingObjToPadicAlgCl`.

All already stated proof-dependency modules are imported. The three unstated
proof dependencies `det-prop-scalar-six-ctf`,
`lem-sfb-finite-ring-relative-scalar-comparison`, and
`lem-sfb-integral-finite-scalar-perfect-model` have no recorded module to import;
they remain explicitly cited in the proof docstring. They are proof inputs,
not missing notions needed to type this statement. No import is added to a
read-only consumer file.

Edge cases checked before writing and during the second pass: empty schemes;
zero complexes; the zero finite ring (ell^0 annihilation forces exactly that case);
identity scheme maps; identity finite and finite-field/integer coefficient maps;
empty coefficient composites at the algebraic-closure endpoint; nonflat maps
Z/ell² → F_ell; continuous integral-to-finite maps without a surjectivity
assumption; arbitrary positive-characteristic base fields; all ambient unbounded
objects in the coherence identities. Dctf is essential for invertibility and is
not required for coherence. Finite rings live in the same arbitrary `Type u`
as schemes, so no independent too-small universe makes their hypothesis vacuous.
The fixed finite-subfield arithmetic parameters live in Type 0 as in the recorded
coefficient convention; the site and section groups remain universe polymorphic.

Searches: `msearch.py` LeanFinder queried derived coefficient/direct-image
comparison (eight differential-module hits, no match); Loogle queried
`SheafOfModules.pushforward, CategoryTheory.IsIso` (three underived adjunction,
quasicoherence and unit hits); Mathlib grep queried
`extendScalars.*lowerStar|lowerStar.*extendScalars|scalar.*direct.image` (no hits).
`rg` on both project roots found the canonical mate/coherence module, which is
used, and strict/completed/finite specializations, none stating this result.
DAG and blueprint searches for `listed coefficient` found four consumers but no
separate definition. LeanSearch for finite composites of continuous coefficient
maps returned eight generic affine, completion and PadicInt maps. Loogle's
`MorphismProperty.multiplicativeClosure` query reported an unknown identifier;
source inspection found the generic closure, which does not define these
specific generators. Mathlib/project grep for `ListedCoefficientMap`,
`IsIntegralFiniteScalarMap`, and `listed.coefficient.map` found no definition.
An additional LeanFinder query for the six families returned perfectoid period
rings, finite adeles and Fontaine theta, no match. Exact query output is retained
in the new node's mathlib_searches.

Validation: scompile.py compiled each of the two modules independently in
sandbox and library modes against the live published library. Final runs were
clean, without warnings. The initial finite-map section binder incorrectly
requested a topology on A outside the canonical finite coefficient sheaf; it
was repaired by using that sheaf's actual section type. No topology assumption
was added. No statement dispute or source correction is needed.

## New nodes

`def-sfb-listed-coefficient-maps` defines `ListedCoefficientMap` and its
continuous integral-to-finite predicate in `Sheaf.SixFunctors.ListedCoefficientMaps`.
Its source is the current unit's coefficient list (1)--(4). The six constructors
are: finite ring homomorphisms characterized by pointwise postcomposition;
integer-ring inclusions identified with `finiteCoefficientIntegersPointMap`;
field inclusions identified with `padicSubfieldRingObjMap`; valuation-ring
localization identified with the existing condensed inclusion; inclusion into
the finite-subextension-valued algebraic closure; and integral-to-finite maps
with an explicitly continuous ring homomorphism and the section formula.
The composition constructor takes actual categorical composites. An explicit
identity at Qbar includes the empty composite; other endpoint identities are
already elementary generators. The finite coefficient endpoint is the existing
`cartesianFinitePointRing`, which fixes its discrete topology.
The searches above show why this list needs a node; its underlying rings, maps,
scalar extension and canonical mate were all reused. The helper predicate's
`letI` is definition-body topology installation, not a hidden binder in a theorem.

## Second reading by NS

A separate second pass by this worker compared both files against the entire
node and current source. No additional agent was started, as the dispatcher
brief prohibits it. The independent maintainer review remains the external
second reader.

This pass checked all standing binders, both Dctf outputs, the orientation of
all four ambient equations, the gamma definition in the imported mate module,
and all six coefficient constructors. It found no omitted clause or extra
mathematical hypothesis. In particular: finite maps are not required flat;
integral-to-finite maps are continuous into the discrete topology, not an
arbitrary map of condensed objects; Qbar uses the finite-subextension convention;
and the final two equations use the inverse theta and the actual adjunction
units and counits. The initial topology elaboration defect described above
was corrected before validation. No dependency record was replaced and no
existing mathematical node statement was changed.
