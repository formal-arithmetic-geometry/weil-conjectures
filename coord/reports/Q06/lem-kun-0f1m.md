## Worker report

Item: `lem-kun-0f1m`, group Q06, stage 2, 2026-10-16.
Module: `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution`.
Main declaration:
`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE_iff_exists_kFlat_flat_model`.
The original node statement and all dependency lists are unchanged. No statement correction,
new DAG node, or dependency-record repair is needed. Nothing is proved: the main theorem
and the named scalar-restriction additivity theorem have `sorry` proofs. Every definition
has explicit data, with the functor laws proved as structure fields of that construction.

Source reading: [Stacks 0F1M](https://stacks.math.columbia.edu/tag/0F1M), entire statement
and proof, and [Stacks 0G7E](https://stacks.math.columbia.edu/tag/0G7E), entire statement
and proof. The local literature source paths named by the node are absent in this read-only
clone, so the corresponding public Stacks pages were opened. The source gives precisely
the lower Tor-amplitude equivalence and the stable choice of a representative. The node's
extension from ringed-site morphisms to ringed-topos morphisms is supplied by 0G7E.
The main docstring records all seven steps of the node proof, including the quotient
map K -> P, the boundary cokernel, and the degreewise tensor short-exact-sequence
argument in place of an unjustified homotopy-category cone argument.

Clause-by-clause correspondence:

- Commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ]`. No nonzero, finite,
  Noetherian, torsion, characteristic or invertibility hypothesis is added.
- Scheme T and its small etale site: `(T : Scheme.{u})`, always using
  `T.smallEtaleTopology` on `T.Etale`. Objects have universe `u+1`, morphisms `u`.
- Constant coefficient sheaf Λ_T: `torModelCoefficientRing Λ T` is literally
  `(constantSheaf T.smallEtaleTopology CommRingCat).obj (CommRingCat.of Λ)`;
  `torModelRing` applies `sheafCompose` with the forgetful functor to rings.
  These are transparent abbreviations of the existing constant-sheaf construction.
- E in D(T_et,Λ): `(E : DerivedCategoryModule Λ T)`, the existing
  module-valued-sheaf derived category used by `def-weil-pbc-derived-categories`.
- Integer a: `(a : ℤ)`, with no sign restriction.
- Lower Tor amplitude: `DerivedCategory.hasTorAmplitudeGE Λ T a E`, the exact
  recorded predicate, testing every module-valued sheaf in degree zero with the
  existing `Etale.derivedTensor` and requiring zero cohomology in every degree i<a.
- The equivalence: the main connective is `↔`; both directions are retained.
- A representing cochain complex: `∃ P : CochainComplex
  (SheafOfModules.{u+1} (torModelRing Λ T)) ℤ`. Representation means
  `Nonempty (DerivedCategory.Q.obj
  (((torModelRestriction Λ T).mapHomologicalComplex (.up ℤ)).obj P) ≅ E)`.
  This is representation up to isomorphism in the specified derived category,
  rather than equality of selected complexes or a hypothesis selecting E.
- K-flatness: `CochainComplex.IsKFlatIndependentCoefficients
  (R := torModelCoefficientRing Λ T) P`, the exact predicate of the recorded
  ringed-topos pullback statement. It tests acyclicity against arbitrary unbounded
  complexes using the sheafified direct-sum total tensor with the Koszul signs.
- Flat terms: `∀ i : ℤ, SheafOfModules.IsFlatOnSite
  (J := T.smallEtaleTopology) (R := torModelCoefficientRing Λ T) (P.X i)`.
  This is the recorded exactness predicate for the sheaf tensor functor, not
  sectionwise flatness or an assumption on the coefficient ring map.
- P^i=0 below a: `∀ i : ℤ, i < a → IsZero (P.X i)`. No upper bound is imposed.
  Categorical zero is the standard invariant reading of a vanishing module sheaf.
- The moreover assertion belongs to the SAME P: the universal pullback clause
  is a conjunct inside `∃ P`, following its representation isomorphism. There is
  no fresh P in that clause and no restriction of P to a bounded complex.
- Arbitrary target site/topos: `{D : Type uD} [Category.{vD} D]
  [EssentiallySmall.{u+1} D]`, `(J : GrothendieckTopology D)` and
  `(RI S : Sheaf J CommRingCat.{u+1})`. Both site universes are independent of
  those of T. Relative essential smallness and coefficients in u+1 are exactly
  the size convention and the recorded general pullback interface, not a
  site-object/morphism universe equality.
- Morphism of topoi: `uInv`, `uPush`, `(_adj : uInv ⊣ uPush)` and
  `[PreservesFiniteLimits uInv]`. This includes morphisms induced by sites.
- Ring homomorphism and module pullback: `I : AlgebraicInverseImage uInv
  (torModelCoefficientRing Λ T) RI`, `(c : RI ⟶ S)` and the additive functor
  `uStar`, with `hobj` and `_hmap` identifying its objects AND maps with
  `SheafOfModules.changeOfRings c` applied after `I.modules`. Thus it is precisely
  inverse image followed by extension of scalars; it is not an arbitrary functor
  or an arbitrary map between the two coefficient sheaves.
- Termwise pullback: `((uStar.mapHomologicalComplex (.up ℤ)).obj P)`.
- Both pullback conclusions: `IsKFlatIndependentCoefficients (R := S) ... ∧
  ∀ i : ℤ, IsFlatOnSite (J := J) (R := S) (... .X i)`.
  There is no assumption that c is flat or that module pullback is exact.

The canonical encoding transport is construction data, not an axiom or a choice:
`torModelScalarUnit` is `toSheafify` on the constant commutative ring presheaf,
whiskered by the forgetful functor to rings. `torModelRestriction` applies
`PresheafOfModules.restrictScalars` to this unit; its sections, differentials and
maps are unchanged as abelian groups. `Presheaf.isSheaf_of_isSheaf_comp` proves the
module-valued presheaf is a sheaf. The named theorem `torModelRestriction_additive`
records additivity, with its pointwise proof plan; this is the only postponed fact
the definition of the termwise transport requires. It belongs to the representative
encoding in this node, and is listed in `lean.declarations`.

Search found the older `Scheme.etaleConstantModuleRestrictionFunctor` in
`Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`: it has source modules
over sheafification in RingCat, whereas the recorded flat/K-flat predicates take
modules over the forgotten CommRingCat sheafification. Those ring sheaves are not
definitionally equal. `ModuleSheafConstantRingEquivalence` supplies an existential
equivalence but its concrete functors are private and it does not select the needed
canonical scalar restriction. The helper here uses the existing restriction-of-scalars
construction at the actual ring sheaf, with exactly the same underlying sheaf, and
never chooses an arbitrary equivalence. These helpers implement the permitted
canonical coefficient transport in the owning node's module.

Dependency declarations used (full signatures/docstrings inspected):

- `def-kun-constant-sheaf`: `Mathlib.Algebra.Homology.Additive`,
  `CategoryTheory.Functor.mapHomologicalComplex`, specialized termwise; the
  constant ring itself is the existing `CategoryTheory.constantSheaf`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`, with
  `ofArrows_mem_smallEtaleTopology_iff` specifying the jointly surjective covers.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  the publicly imported `AlgebraicGeometry.Etale.DerivedCategoryModule`; the
  unrelated torsion-cohomology predicate is not substituted for the category.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`,
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`, used through `hasTorAmplitudeGE`.
- `def-pc-flat-sheaf-modules`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `lem-weil-pbc-ringed-topos-kflat-pullback`:
  `Sheaf.Paper.KFlatRingedToposPullback`, `SheafOfModules.isKFlat_ringedToposPullback`.
  The published compiled signature uses `IsKFlatIndependentCoefficients`, as in
  its DAG record. This was checked through scompile.py and the server source reader.
- Proof-only imports retain all recorded modules currently stated:
  `Sheaf.Paper.EtaleFlatKFlatResolution`,
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES`,
  `Sheaf.Paper.EtaleKFlatCriteria`, and
  `Sheaf.Algebra.Homology.FilteredColimitsTensor`.
  The two proof dependencies `lem-kun-tor-cokernel-flat` and
  `lem-weil-pbc-complex-ses-homology-long-exact` have no recorded Lean module,
  so there is no module to import for them. They are not needed to type this
  statement. `def-weil-size-convention` is a metatheoretic convention with no module.

Edge cases checked: empty scheme; zero coefficient ring; zero E; arbitrary negative,
zero or positive a; unbounded-above E and P; no upper amplitude bound; arbitrary
acyclic tensor tests; identity and nonflat coefficient maps c; a target site with
different object/morphism universes; disconnected schemes and infinite modules.
No condition excludes these cases. The zero complex supplies the expected model
of zero. At degree a no vanishing is required. The same complex must satisfy all
pullbacks, rather than choosing a complex after each pullback.

Searches (Q06, this session):

- msearch LeanFinder: “Tor amplitude bounded below iff bounded below K flat complex
  of flat module sheaves”. Eight hits on `DerivedCategory.isGE_Q_obj_iff`, `isGE_iff`,
  support and single objects. They do not assert flat terms, K-flatness or pullback
  stability, so none is the target theorem.
- msearch Loogle: `CochainComplex.KFlat, ObjectProperty.flat`. No hits; the service
  index does not know that upstream KFlat name.
- msearch grep: `torAmplitude|KFlat` in `Algebra/Homology`. No hits in Mathlib.
- msearch LeanSearch: the lower Tor-amplitude/K-flat-model query. Service unavailable
  with Internal Server Error; no match verdict is inferred from its unavailability.
- rg of Mathlib, WeilConjectures and lean/Sheaf for Tor amplitude, KFlat, IsFlatOnSite,
  derived category representatives and constant-ring module equivalences. Found the
  cited definitions and the transport interfaces described above, but no exact theorem.
  `Sheaf.Algebra.Homology.TorAmplitudeFlatModel` concerns ordinary modules and a
  bounded interval [a,b], so does not give this arbitrary etale-site lower-bound result.
- rg of WeilConjectures for `lem-kun-0f1m`: no result. rg of upstream-name inventory,
  Mathlib, WeilConjectures and lean/Sheaf for the new full declaration names:
  no pre-existing declaration.

Validation: scompile.py Q06 lem-kun-0f1m compiled the completed file separately in
sandbox and library positions, with no errors and no warnings (9.2 s / 12.0 s).
An earlier stale overlay contained duplicate K-flat artifacts; the final local overlay
compiles successfully with the recorded imports. No statement dispute remains.

## Second reading by Q06

I reread the unit statement in `dag/nodes/sec-smooth-purity/lem-kun-0f1m.json`, the
complete module, the recorded dependency signatures, and Stacks Tags 0F1M and 0G7E.
The source statement is for a ringed site and says: (1) a ringed site, an object `E` in
its derived category, and an integer `a`; (2) the equivalence between Tor-amplitude
below `a` and a K-flat complex of flat modules vanishing below `a`; and (3) one such
representative whose pullback along every ringed-topos morphism is K-flat with flat
terms. The unit specializes the site to `T.Etale` with `torModelCoefficientRing` and
spells out the pullback data required by the recorded general theorem.

Object and hypothesis check, in order:

- The commutative ring is `(Λ : Type (u + 1)) [CommRing Λ]`; the scheme is
  `(T : Scheme.{u})`; there are no nonzero, Noetherian, finiteness, characteristic, or
  sign assumptions. The coefficient ring is exactly the Mathlib constant sheaf
  `torModelCoefficientRing Λ T`, and `torModelRing` is its canonical forgetful image.
- `E : DerivedCategoryModule Λ T` is the dependency's derived category of sheaves of
  `Λ_T`-modules, and `a : ℤ` has no sign restriction. The left side is exactly the
  recorded `DerivedCategory.hasTorAmplitudeGE Λ T a E`, whose quantifiers range over
  every module sheaf in degree zero and every `i < a`.
- The right side introduces one `P : CochainComplex (SheafOfModules
  (torModelRing Λ T)) ℤ`. Its four consecutive clauses render K-flatness with the
  recorded independent-coefficients predicate, flatness of every term with the
  recorded `IsFlatOnSite` predicate, `IsZero (P.X i)` for every `i < a`, and
  `Nonempty (DerivedCategory.Q.obj (((torModelRestriction Λ T).mapHomologicalComplex
  (.up ℤ)).obj P) ≅ E)`. Thus representation is in the specified derived category,
  up to isomorphism, using the canonical scalar restriction; no equality or selected
  representative is imposed.
- The final conjunct quantifies arbitrary `D`, its category and essential-smallness,
  `J`, coefficient sheaves `RI` and `S`, an adjoint pair `uInv ⊣ uPush` with
  `PreservesFiniteLimits uInv`, the algebraic inverse-image datum `I`, and a ring map
  `c : RI ⟶ S`. The functor `uStar` is required on objects and maps by `hobj` and
  `_hmap` to be precisely inverse image followed by `changeOfRings c`, and it is
  additive. The two conclusions are exactly K-flatness over `S` and flatness of every
  pulled-back term. This is the full interface of
  `SheafOfModules.isKFlat_ringedToposPullback`, so arbitrary ringed-topos pullbacks,
  including identity and nonflat coefficient maps, are represented.

The connective is `↔`, the representative is chosen once before the universal
pullback quantifier, and all quantifiers occur in the source order. There is no extra
upper bound, boundedness, exactness of pullback, or flatness assumption on `c`.
`torModelScalarUnit` and `torModelRestriction` are real canonical constructions; the
only postponed helper is the named `torModelRestriction_additive` theorem, whose
docstring gives its source and pointwise proof. No hollow definition or unbound
variable occurs, and the node's `lean.statement` is byte-for-byte the theorem
signature in the module.

Edge cases checked: empty or disconnected schemes, the zero coefficient ring, the zero
derived object and zero complex, arbitrary negative/zero/positive `a`, no upper bound,
unbounded complexes, identity and nonflat `c`, empty target sites, and target sites
with independent object and morphism universes. Degree `a` is allowed, and only
degrees strictly below `a` must vanish. The same `P` is used for every pullback.

For the independent existing-declaration search I ran LeanFinder for a lower
Tor-amplitude/K-flat model, Loogle for `CochainComplex IsKFlatIndependentCoefficients
IsFlatOnSite`, and `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for
Tor-amplitude, K-flat models, the exact theorem name, and the scalar-restriction
helpers. LeanFinder returned only ordinary `DerivedCategory.isGE_Q_obj_iff` and
single-ring flatness results; Loogle returned no K-flat hit; the grep search found
only the cited generic definitions and pullback theorem. LeanSearch was unavailable
with an internal-server error, which is recorded in `searches.jsonl`. No exact
existing declaration was found.

No mismatch was found, so no Lean, node, dependency record, or statement correction
was needed. The module was rechecked with `scompile.py`; the prior clean compile and
the server confirmation cover the recorded imports.
