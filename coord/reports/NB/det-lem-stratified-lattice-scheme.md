## Worker report

Item: det-lem-stratified-lattice-scheme. Group: NB. Stage: 2.
Module: `Sheaf.Paper.StratifiedLatticeScheme`.
Main declaration:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_stratifiedLatticeScheme`.

The theorem states all three conclusions for the actual pulled-back condensed
coefficient ring and an internal module L. Its sole postponed proof is `by sorry`.
The seven helper definitions have real data; none chooses data from an unproved
existence theorem. No source statement, proof or proof dependency was changed.
Four already landed definition nodes and the new existing:true definition node
`def-sfb-integral-lattice-pairs` record the exact interfaces used. The returned
theorem dependency is replaced by this definition owner; the Lean file is retained.

Source read: current main-20261015 blueprint,
`sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice-scheme.md`
and the adjacent `.proof.md`, including the coefficient convention, embedded-image
identification, explicit ind-quasi-affine fpqc descent and universal section.
The source and the DAG agree. No STATEMENT-DISPUTED finding.

Hypotheses and conventions, individually:

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. No extra norm or topology is assumed.
* Canonical topology: `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)`
  transports the given finite extension to its canonical absolute-value topology.
  `latticeCoefficientIntegers l E` is the transported valuation subring from
  `Padic.coefficientExtensionIntegers`, with its induced topology. This is O_E,
  not an arbitrary subring.
* The condensed topological rings are the existing
  `Profinite.continuousCoefficientRingObj` applied to those two topological rings.
  The helpers `latticeCondensedField` and `latticeCondensedIntegers` are abbreviations.
  `latticeCondensedRingInclusion` postcomposes each continuous function with the
  actual valuation-subring inclusion. `latticeCondensedInclusion` forgets to the
  underlying abelian sheaves and bundles the same ring morphism using `Mon.ofHom`.
* Pulled-back coefficients: the type of L is literally
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})
  (condensedRingObj (latticeCondensedField l E) X)`. Thus E_X is the recorded
  inverse image of the condensed ring; it is not replaced by a constant sheaf.
  The integral scalar map uses `coefficientMap` on the actual inclusion.
* Internal module convention: L is an internal `CategoryTheory.Mod` object.
  `stratifiedLatticeModule` applies the existing `sectionModuleEquivalence`,
  explicitly at universes `{u+1,u+1,u}`. This equivalence preserves the underlying
  abelian sheaf, all section groups and restriction maps identically.
  `stratifiedLatticeScalarMap` uses the existing `sectionRingMap` applied to the
  actual pulled-back inclusion. `stratifiedLatticeSectionRing` is the same
  reconstructed rational ring after forgetting commutativity. No unrelated
  continuous coefficient ring or arbitrary comparison map is substituted.
* Small pro-etale site: `Scheme.ProEt.topology X`, with objects `X.ProEt`.
  `F.over V` and module `.over V` use the recorded localized site.
* Universe convention: schemes and coefficient carriers are in u; site objects
  are in u+1, morphisms in u, abelian sections in u+1 and lattice classes in u+2.
  Every universe and term variable is explicit (`autoImplicit false`). The lifted
  finite index and lifted quotient only implement the containing-universe
  convention; neither changes the underlying finite free module or coset set.
* qcqs: `[CompactSpace X] [QuasiSeparatedSpace X]`. The latter is the recorded
  scheme equivalent of quasi-compact diagonal, not separatedness of X.
* Constant rank r: `(r : ℕ)` and `_hL` give a covering family of pro-etale objects
  together with rank-r free trivializations. `CoversTop U` is the site's covering
  condition; free modules have index `ULift.{u+1} (Fin r)`. This is precisely
  pro-etale locally finite free of the fixed rank, including zero.

The lattice object and every conclusion:

* `IntegralLatticePair a L U` consists of an integral module M, its
  `IsFiniteLocallyFree` property on the localized site, and the rationalization
  isomorphism `changeOfRings (latticeScalarMap a U) M ≅ L.over U`. For the actual
  O_E -> E map, rational scalar extension is inversion of ell, so this is exactly
  M[1/ell] = L|U. This is a conclusion's data, not an added hypothesis on the input.
* A pair represents an embedded module by its image
  `m ↦ alpha(eta(1 ⊗ m))`. The map is injective: locally M is free and the integral
  coefficient inclusion is injective, hence this holds after rationalization on
  each free chart and descends. Conversely an embedded lattice supplies that pair.
  The existing pair-image classification proves that equality of images is
  exactly intertwining integral isomorphism, uniquely. Thus quotienting pairs
  retains precisely embedded submodules, not abstract isomorphism classes of
  integral modules that forget their position in L.
* `∃ F c, IsLatticeClassPresentation a L F c` identifies F with the sheaf described
  in the node. The presentation has three substantive clauses: every section is
  represented by a lattice pair; two pairs give equal sections exactly when their
  rationalizations intertwine; restriction along every f is characterized by
  equality of embedded images on every test object of the slice. Consequently
  both its values and its restriction maps are specified; F is not an arbitrary
  sheaf with a bare bijection of global sections.
* Clause (1): for every `V : X.ProEt` and every rank-r free trivialization `_t`,
  `Nonempty (F.over V ≅ (constantSheaf ...).obj
  (ULift.{u+2} (integralMatrixCosets (latticeCoefficientIntegers l E) r)))`.
  `integralMatrixCosets A r` is GL_r(E) modulo the image of GL_r(A) by right
  multiplication, i.e. the cosets g GL_r(A) corresponding to g A^r. `constantSheaf`
  is the actual sheafification of the constant presheaf, not a constant presheaf.
* Clause (2): `∃ Q : X.ProEt, IsSeparated Q.hom ∧ Etale Q.hom ∧ Surjective Q.hom`.
  The representing scheme has underlying scheme Q.left and structure map Q.hom.
  It is legitimate to use a site object: etale implies weakly etale. No
  quasi-compactness, finite type, finiteness or properness of Q -> X is assumed.
* Representation is the natural isomorphism `ρ` from F.obj to the restricted
  Yoneda presheaf `((Scheme.ProEt.forget X).op ⋙ yoneda.obj (Over.mk Q.hom))`,
  lifted to the sheaf-value universe. At U its value is exactly Hom_X(U,Q).
  Thus this asserts representation on every pro-etale test object and naturality
  in every site morphism, rather than a mere bijection on selected sections.
* Clause (3): `∃ M : IntegralLatticePair ... Q` with
  `(ρ.hom.app (op Q) (c Q M)).down = 𝟙 (Over.mk Q.hom)`.
  The pair gives the actual embedded universal integral lattice in L|Q = q*L.
  Its section is required to classify the identity. By the naturality of ρ and
  the image-restriction clause of the presentation, pulling it back along any
  U -> Q gives exactly the lattice classified by that map. This is the universal
  property, not merely existence of some lattice on the representing scheme.

Recorded dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly supplies the
  constructions in `CoefficientExtension`: `Padic.coefficientExtensionAbsoluteValue`
  and `Padic.coefficientExtensionIntegers` (the finite extension's canonical ring).
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `.topology`, `.forget`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.condensedRingObj`, `coefficientRing`, and the
  coefficient object pulled back by `upperStarFromPoint`; module objects use
  `CategoryTheory.Mod` from the recorded Mathlib monoidal-module definition.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.Etale`: `IsSeparated`, `Etale`;
  `Surjective` is the usual underlying-map property of a scheme morphism.
  The size and scheme-convention dependencies are conventions, with no private
  replacements: the signature uses their explicit universes and qcqs predicates.
* Added landed node `def-sfb-continuous-lattice-coefficients`:
  `Sheaf.Paper.LatticeSheafBasic`, `latticeCoefficientIntegers`.
* Added landed node `def-weil-pbc-internal-abelian-sheaf-module-equivalence`:
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and
  `.sectionRingSheaf` (full signatures and construction read).
* Added landed node `def-weil-pbc-continuous-coefficient-module-encoding`:
  `Sheaf.Paper.ContinuousCoefficientModuleEncoding`,
  `AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap`. Its signature is generic
  in the ring objects; the Type-0 specialization of continuousRingModuleEquivalence
  is not used and imposes no restriction on E here.
* New existing:true definition node `def-sfb-integral-lattice-pairs`:
  `Sheaf.Paper.LatticeSheafBasic`, `latticeScalarMap`, `IntegralLatticePair`,
  `.Equivalent`, `.image`, `IsLatticeClassPresentation`, `integralMatrixSubgroup`,
  and `integralMatrixCosets`. The image-classification theorem is a proof fact;
  its result is not used to construct the statement or its helpers.
* Added landed node `def-weil-pbc-condensed-e-module-category`:
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`, publicly reexporting
  `ContinuousCoefficientUniverse`, with `Profinite.continuousCoefficientRingObj`,
  `.continuousCoefficientRingSheaf` and `.isCommMonObj_continuousCoefficientRingObj`.
  These accept T : Type u, so no Type-0-only coefficient API is imposed.

All proof dependencies with stated modules are imported without `public` unless
needed also by the signature. Mathlib matches are covered by Affine,
QuasiSeparated, AffineScheme, Limits, Fpqc and Precoverage. In particular the
upstream fpqc etale-descent module is imported, avoiding its retired Sheaf twin.
The theorem docstring gives every DAG proof step: coefficient comparison and
localization, embedded pair classification, finite affine pro-etale fpqc cover,
clopen descriptions of maps to coproducts, transition cocycle, ind-quasi-affine
effectivity, etale/separated descent and surjectivity, representability by fpqc
gluing, and the identity section yielding the universal lattice.

Edge cases checked before finalizing the statement:

* r=0: Fin 0, the trivial GL_0 quotient, the zero integral lattice, and Q=X.
* X empty: the empty trivializing family is allowed; all sheaf values are terminal
  and the empty representing scheme is surjective over the empty base.
* V empty: the local constant-sheaf conclusion is still the unique empty-site sheaf.
* Arbitrarily large/infinite lattice set: its lift affects only universe encoding;
  no quasi-compactness or finite-component hypothesis is placed on Q.
* Nonseparated qcqs X: separatedness is required only of Q -> X.
* No condition that ell be invertible on X, no characteristic, positive-rank,
  Noetherian or nonempty-base hypothesis is added.
* Different trivializations and different presentations of an embedded lattice:
  the quotient uses intertwining rationalizations and its restrictions preserve
  images, so it does not forget the embedding or depend on chosen bases.

Searches (prescribed msearch wrappers plus the named read-only source trees):

* leanfinder: "The sheaf of integral lattices in a lisse p-adic local system is
  represented by a separated surjective etale scheme". Eight hits: BDeRham,
  BDeRhamPlus and generic Scheme.Etale category declarations; no exact theorem.
* loogle: `AlgebraicGeometry.Scheme, "lattice"`. Three Scheme.IdealSheafData
  order-lattice instances; no match.
* grep in Mathlib/AlgebraicGeometry: `[Ll]attice|[Ll]isse`. Nine generic lattice
  hits; no p-adic lattice-scheme statement.
* leansearch: "embedded integral lattices in internal modules over a condensed
  ring". Eight generic Submodule.IsLattice / CondensedMod hits; no exact match.
* leanfinder: "Embedded lattices as subobjects of a rational sheaf of internal
  modules with invertible scalar extension". Eight generic condensed-module,
  tilde and free constructions; no exact match.
* grep: `EmbeddedLattice|LatticeAt|lattice.*subobject`. Eight generic subobject
  lattice-theory hits; no actual pro-etale integral lattice scheme.
* rg in lean/WeilConjectures and lean/Sheaf for lattice-scheme and representability
  names, and literal item id in WeilConjectures: no existing theorem of this node.
  The broader lattice search located LatticeSheafBasic/LocallyConstant, reused here,
  and the generic section-module equivalence, also reused rather than copied.
* DAG search for embedded lattice and tools/blueprint_refs.py search "embedded
  lattice": no independent missing embedded-lattice definition. Search "lattice"
  found 39 nodes, including the recorded pair-image/local-classification interfaces.
  `blueprint_refs.py ancestor det-lem-stratified-lattice-scheme` identifies the item
  as a detail of the stratified-lattice unit. No parallel notion was introduced.

Compilation: prescribed `scompile.py NB det-lem-stratified-lattice-scheme` compiled
both the sandbox statement and its actual library module, without errors or
warnings, in approximately six seconds each. The initial unresolved section-ring
universe was repaired by giving the existing equivalence explicit universes;
this adds no mathematical assumption. Final dry run and delivery use deliver2.py.


## New nodes

`def-sfb-integral-lattice-pairs` records seven existing definitions in
`Sheaf.Paper.LatticeSheafBasic`: slice scalar restriction; the finite locally free
module with its scalar-extension isomorphism; equivalence by intertwining integral
isomorphisms; its sectionwise image under the sheafification unit; the three-clause
lattice-class presentation; and the integral matrix subgroup and its coset set.
Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, pp. 59--60, read from the local
PDF; the blueprint's lattice-scheme statement uses exactly this lattice functor
and these cosets. The generic ring-sheaf interface states definitions only: it
does not assert injectivity or image classification for an arbitrary ring map.
The node's `lean.statement` is the verbatim `structure IntegralLatticePair`
signature through the last binder, before `where`; all seven full declaration
names are listed in `lean.declarations`. Existing:true introduces no Lean file.

Searches for this repair: LeanSearch returned eight scalar-extension and
intertwining-map hits, LeanFinder returned eight generic quasicoherent-presentation
hits, and the Mathlib grep returned zero hits; their exact wrapper queries and
returned names are in the new node's `mathlib_searches`. Searches of
`lean/WeilConjectures` found no declaration; `lean/Sheaf` found the published seven
definitions and their consumers. The DAG declaration-record scan found no
existing definition owner. `blueprint_refs.py search 'lattice pair'` returned zero
nodes; search 'integral lattice' returned seven unrelated blueprint nodes.
`def-sfb-continuous-lattice-coefficients` owns only the coefficient constructions.
Thus the new node reuses the existing definitions without duplicating them.

## Repair of immutable-head 81e6cb0c0b67 H2

The initial required dry run of the retained packet passed at 94cfbecc00e.
The saved packet differs from the current read-only repository only in the item's
`lean` and `stmt_deps`; its mathematical statement and proof plan are identical.
The seven definitions were read in full at LatticeSheafBasic lines 76--232.
The only requested repair is now made: the item's statement dependencies cite
`def-sfb-integral-lattice-pairs` in place of the theorem node
`lem-weil-pbc-lattice-pair-image-classification`. The statement does not select
anything from that theorem. No source or Lean statement was changed.

## Second reading by NB

This is the dispatcher's single-worker repair self-check; no independent worker
is claimed. The maintainer's independent reading accepted every mathematical
clause at the returned head, and the Lean module is retained byte for byte.
I checked the new node against the existing declaration bodies: `latticeScalarMap`
is slice restriction; `IntegralLatticePair` has precisely module, locallyFree and
rationalization fields; `.Equivalent` is existence of an intertwining isomorphism;
`.image` is the range of alpha applied to the sheafification unit on 1 tensor m.
`IsLatticeClassPresentation` has exactly surjectivity, exact kernel relation and
the restriction/image iff on every test object. `integralMatrixSubgroup` is the
range of the matrix-group inclusion, and `integralMatrixCosets` is its gH quotient.
No image-classification theorem is asserted as a definition, and no coefficient
sheaf definition is re-owned. Rank zero, empty slices and varying local ranks
remain allowed; arbitrary ring maps require no injectivity to define these data.
All seven declarations have real bodies. Only the existing item theorem is
postponed with sorry. The new definition node is cited directly by the item.


Repair validation: the prescribed scompile.py compiled both the sandbox statement
and its actual module cleanly (6.1 s and 6.4 s). A structural self-check confirms
that only the item's permitted lean/stmt_deps fields differ from current main,
all original dependencies remain, the new node's citations equal its stmt_deps,
and both recorded signatures are verbatim. The Lean file SHA-256 is
68e87efa4ebc306bbb1df54c15007bcd622c1382048649693e059abf495e1a75.
The first repaired-packet preflight requested blueprint.from.via=[] because the
item is itself the ancestor blueprint node; this metadata is corrected. The dry
run compiles the existing declaration module as well as the delivered item.
