## Worker report

The module `Sheaf.CategoryTheory.NormedScalarProfiniteHomAcyclic` states
`Profinite.NormedScalarHom.normed_scalar_profinite_hom_acyclic` with `sorry`.
All other declarations are real constructions or the transparent full comparison
predicate `Assertion`. There are no additional postponed theorems, dependency modules, or changes to
the natural-language statement. Two new existing:true definition nodes own
already constructed interfaces, repairing return H2.

This repairs the return on immutable head `e8abced2b64d`. The saved packet's
initial dry run passed, but that mechanical pass did not repair the reviewer's
H2 finding. The Lean module is retained verbatim. The current live item still
has only its original four statement dependencies and no Lean binding. Its
statement, proof, sources and all other fields are retained from that base;
only the authorized `stmt_deps` and `lean` differ.

Hypotheses and clauses, matched individually:

- A prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- A finite extension E of Q_ell with its extending norm topology:
  `(E : Type u) [NormedField E] [NormedAlgebra ℚ_[ell] E]
  [FiniteDimensional ℚ_[ell] E]`. The normed algebra structure makes the
  algebra map compatible with the field norms; no discrete topology or
  algebraic-closure hypothesis is added.
- F=E: the theorem applies every construction directly to `E`.
- A_F(S)=C(S,F), including every continuous function: the existing
  `Profinite.CondensedAction.continuousScalarRing E` bundles the recorded
  `Profinite.continuousMapRingObjOfUniverse` and its actual canonical monoid
  structure and commutativity witness. This is not a constant ring sheaf.
- The coherent profinite site and the size convention: `Profinite.{u}` with
  `coherentTopology`, coefficient groups in `u+1`, internal module objects
  in `u+2`, and `HasDerivedCategory.standard` with localization universe
  `u+2`. The bound u contains both E and the profinite parameters, exactly
  the already landed bundled-scalar convention. Every universe and binder
  is explicit; `set_option autoImplicit false` is enabled.
- Ordinary internal modules: `CategoryTheory.CondensedBar.Modules` is the
  existing `CategoryTheory.Mod`, with its existing abelian structure.
  No solidification, analytic-module category, or completion is used.
- A profinite parameter P: all occurrences quantify over `P : Profinite.{u}`.
- A_F[P], free over the representable condensed set: the existing
  `CategoryTheory.CondensedBar.freeParameter` is the free abelian sheaf
  followed by `Mod.free`, on the existing `uliftYoneda` object.
  `generator` uses the unit of `InternalBar.freeAdjunction` at exactly this
  representable; the definition includes arbitrary continuous S-to-P maps.
- Internal Hom means the right adjoint of relative tensor: `homFunctor`
  is exactly the existing `Mod.ihom (freeParameter ... P)` and its counit
  is the existing `Mod.ihomAdjunction` counit. No arbitrary functor or
  comparison morphism is assumed.
- The module C_F(P) is realized as `(homFunctor E P).obj (Mod.regular A.X)`.
  Its identification with the displayed sections C(S x P,E) is not merely
  asserted informally: `Assertion` first states that the explicitly defined
  `evaluation E P S` is bijective, for every P and S.
- This evaluation is precisely the specified evaluation identification.
  Pull the Hom section along S x P to S; take the universal free generator
  given by S x P to P; form their pure tensor via the lax sheaf-inclusion
  tensor map and the colimit injection defining `Mod.tensorLeft`; apply
  the tensor-Hom counit. The answer is a section of the actual regular
  ring at S x P, and `.down` removes its universe lift. It already is a
  continuous function, with no chosen continuity proof and no existence
  choice of an unspecified function or module.
- A_F(S) acts through the S-coordinate: the second and third conjuncts of
  `Assertion` state additivity of evaluation and
  `evaluation ... (r • x) (s,p) = r.down s * evaluation ... x (s,p)`.
  Together with bijectivity these identify the actual internal module
  with the stated function module. In particular they fix its action.
- Sections restrict along continuous S'-to-S maps: the fourth conjunct
  gives evaluation of the underlying sheaf restriction as f(v(s'),p).
- Derive Hom in its second variable by nonnegative injective resolutions:
  `resolutionAugmentation` applies `homFunctor` to the actual resolution
  inclusion `I.ι`, with the canonical single-complex identification.
  I is any `InjectiveResolution (Mod.regular A.X)`; no special choice or
  extra acyclicity hypothesis is added.
- The canonical comparison is an isomorphism in the ordinary unbounded
  derived category: the sixth conjunct is `IsIso` of the existing
  `Functor.rightDerivedSingleUnit`, whose source is the internal function
  module in degree zero and whose target is the ordinary total
  right-derived Hom evaluated on A[0]. The seventh conjunct also states
  `IsIso` of `DerivedCategory.Q.map` of every zero-extended nonnegative
  `resolutionAugmentation`. Thus the injective-resolution formulation is
  explicit, and the result is an actual derived-category comparison.
- Contravariant naturality for every continuous parameter map: `parameterMap`
  is the actual `Mod.ihomMap` of the free-module map of `uliftYoneda.map v`.
  The fifth conjunct gives f(s,v(p')) on sections. The eighth gives the
  naturality square for these maps on each fixed injective-resolution
  complex, already before localization. Applying Q gives precisely the
  corresponding naturality square of the canonical derived comparisons.
- Degree zero is the evaluation identification: the final conjunct is the
  equation that zeroth homology of the canonical derived single unit is
  the identity after the canonical `homologyRightDerivedFunctorObjSingleFunctorIso`
  and `rightDerivedZeroIsoSelf` identifications. The source module is
  identified with C(S x P,E) by the counit-defined evaluation above.
  Consequently the degree-zero map is this specified evaluation, rather
  than a possibly rescaled abstract isomorphism.
- F=E is complete: the theorem includes `CompleteSpace E` as a conclusion,
  not as an extra hypothesis. Finite dimensionality over Q_ell gives it.
- All continuous functions are retained: the target of evaluation is exactly
  `ContinuousMap`, and bijectivity includes every element of it. No
  `LocallyConstant`, finite-quotient descent, or bounded-image condition
  occurs anywhere in the assertion.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`,
  `continuousMapRingObjOfUniverse`, `continuousMapRingObjOfUniverseMonObj`,
  and `isCommMonObj_continuousMapRingObjOfUniverse`.
- `def-weil-size-convention` is a recorded metatheoretic convention, with
  no declaration; the explicit universes implement it.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and
  `CategoryTheory.Mod.regular`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the
  recorded general ordinary-derived convention; its docstring identifies
  the existing upstream ordinary right-derived functor on these
  Grothendieck module categories. This convention module is imported.
- `Sheaf.CategoryTheory.ContinuousScalarRing`:
  `Profinite.CondensedAction.continuousScalarRing`.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`:
  `CategoryTheory.CondensedBar.Modules`, `sections`, `sectionRing`,
  `sectionModule`, `freeParameter`; and the existing closed module API
  `Mod.ihom`, `Mod.ihomAdjunction`, `Mod.ihomMap`, `Mod.tensorLeftDiagram`.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`:
  `Profinite.CondensedAction.InternalBar.free` and `freeAdjunction`.
- `WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit`:
  `CategoryTheory.Functor.rightDerivedSingleUnit`, with the full signature
  and degree-zero comparison of `rightDerivedSingleUnit_zero` read.

The bundled scalar ring and equivariant bar data are landed definition nodes
and remain in `stmt_deps`. The free adjunction and the derived single unit
are now cited through the two definition records in `## New nodes`, rather
than through the resolution and normalization theorems that happen to host
their declarations. Neither theorem is a statement premise. Dependency
closures were checked: none reaches this item, so these additions close no
dependency cycle.
All recorded modules of the original proof dependencies are imported
non-publicly when not already publicly imported. The analytic Cech lemma
and enough-injectives node have no recorded module; they remain named
proof inputs in the complete proof docstring. Nothing waits on them to
state this item.

Edge cases checked before writing: P empty gives C(S x P,E)=0 and the free
module on P is zero; the zero-to-zero comparison is invertible. For P a
point the function module is A and the comparison is the identity. For S
empty the section groups are zero, including in the evaluation formula.
The identity parameter map and arbitrary compositions use the actual
functorial free maps and tensor-adjunction mates; non-surjective and
empty-domain maps are included. The degree-zero normalization uses the
canonical left-exact identification. No Omega claim is reintroduced: the
live node already restricted the analytic input to complete finite E.

Searches performed for an existing exact statement:

- `msearch.py ... leanfinder`, query: "Derived internal Hom from a free
  condensed module on a profinite set to a complete finite extension of
  the ell adic numbers is the continuous functions in degree zero".
  Eight hits: LightCondensed.ihomPoints and its application formulas,
  Condensed.profiniteFree, LightCondensed monoidal structure, and
  Condensed.profiniteSolid. These concern light/constant coefficient
  modules or ordinary free objects, not this variable-ring ordinary
  derived comparison.
- `msearch.py ... loogle '"Mod.ihom"'`: zero hits.
- `msearch.py ... grep 'profinite.*(acyclic|ihom)|continuous.*(derived|acyclic)'
  Condensed`: zero hits.
- `msearch.py ... leansearch`, query: "Derived continuous functions of
  profinite parameter sets with coefficients in a finite extension of
  the p-adic numbers have no higher internal Hom". Eight hits concerning
  ProfiniteGrp homomorphisms, with no matching acyclicity theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  normed-scalar/profinite acyclicity names, continuous derived Hom,
  free-parameter and scalar-ring names: the only citation of the item is
  in the downstream PrimeToEllCondensedAcyclicity proof. There is no exact
  existing theorem. The searches locate the already landed freeParameter
  and continuousScalarRing constructions; both are reused, not copied.
- Mathlib source and full upstream declarations for Mod, ihom, its
  adjunction, parameter mates, tensor colimit, ordinary derived unit,
  and sectionwise module equivalence were read directly. The older
  CompactObject example is withdrawn on this live checkout and contains
  no declaration; the module follows the current neighboring headers.

The first elaboration diagnosed the distinction between the monoidal
relative tensor encoding and the older `Mod.tensorLeft` colimit encoding.
Evaluation now uses that actual colimit's injection directly, so its
counit is type-correct without an arbitrary tensor comparison. The full
module, including every recorded proof-dependency import, passes
`scompile.py` cleanly. No node fault or statement dispute is identified.

## New nodes

`def-sfb-condensed-free-module-adjunction` owns the existing plain definitions
`Profinite.CondensedAction.InternalBar.free` and `freeAdjunction`, in
`Sheaf.CategoryTheory.CondensedInternalBarResolution`. The node defines the
composite free functor and its composite adjunction on the small coherent
profinite site, including its universal generator. This is precisely the
interface used by `generator` and `parameterMap`. It is sourced to paragraph
(3)'s free internal module construction. It introduces no Lean declaration
and uses no choice from `exists_resolution`. Semantic searches return the
constant-ring and light condensed free adjunctions; the exact variable-ring
internal construction is already present in the project. The definition-node
ownership scan found no definition record on these two declarations; the
bar-resolution theorem lists them as helpers but states a different notion.
`freeParameter` in the existing equivariant-bar-data node specializes this
functor to profinite representables and does not own its adjunction.

`def-sfb-right-derived-single-unit` owns the existing
`CategoryTheory.Functor.rightDerivedSingleUnit` in
`WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit`. Its definition is
exactly localization of the inverse single-complex comparison followed by the
ordinary total right-derived localization unit. The new node follows Stacks
0156 and the recorded unbounded K-injective convention of 070K. It assumes
additivity and K-injective resolutions, without imposing left exactness or
acyclicity. No theorem about the unit is assumed. Semantic searches return
zeroth-derived maps or exact-functor single comparisons; the exact total-derived
unit already exists upstream. The definition-node ownership scan finds no
definition binding to it; the normalization theorem is a separate proposition,
and the shifted-degree comparison node defines a homology isomorphism instead.

Each new node records the actual LeanSearch, LeanFinder, Mathlib grep, project
grep, DAG ownership and blueprint search results in `mathlib_searches`.
Both have `existing: true`, so neither adds a module or a duplicate definition.
The item's additions now cite these definition nodes instead of
`lem-sfb-condensed-internal-bar-resolution` and
`lem-sbc-right-derived-single-zero-unit`. Its original statement is unchanged.

## Second reading by NA

Repair self-check (the maintainer supplies the independent reading; no second
worker was started). I opened the item, its unchanged Lean module, both new
node records, and the full source definitions and their docstrings. The
prime, finite normed extension, actual continuous scalar sheaf, internal free
module, sectionwise evaluation bijection, additive and S-coordinate scalar
laws, both restriction formulas, derived-unit and all injective-resolution
comparison isomorphisms, parameter naturality, canonical degree-zero map, and
completeness conclusion match the clause-by-clause account above. No hypothesis
or clause was changed to repair ownership. The empty profinite parameter,
singleton parameter and empty test object still have the cases recorded above.

For the new free node, the two actual definitions are the composite functor
and adjunction exactly as stated, with no use of `exists_resolution`. For the
new derived node, the actual map is the displayed canonical composite, with
no use of `rightDerivedSingleUnit_zero`; the degree-zero normalization is still
a conclusion of this item's unchanged assertion. Conjuncts eight and nine
were advisory in the return, and have been retained. The only defect found
was the returned H2 theorem/definition ownership mismatch, repaired by the
two definition records and corresponding dependency replacements.
