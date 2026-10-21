## Worker report

The delivery states the canonical dense integer-lattice comparison in the ordinary derived
category of internal modules over the all-continuous coefficient condensed ring. Nothing is
proved: every theorem has a sorry proof with a source and natural-language proof in its
docstring. The item statement and proof are unchanged. The construction helpers are recorded
in lean.declarations in the owning item module; they construct the canonical maps required
to state this item, using the already recorded action and module interfaces.

Clause-by-clause reading:

* Prime ell: the explicit l : ℕ and [Fact l.Prime] binders. An algebraic closure with its
  extended norm is Ω : Type u, [NormedField Ω], [NormedAlgebra ℚ_[l] Ω], and
  [IsAlgClosure ℚ_[l] Ω]. E is an IntermediateField ℚ_[l] Ω with
  [FiniteDimensional ℚ_[l] E]. E uses its induced norm, which extends the original norm.
* Rank: r : ℕ includes zero. AdicLattice l r is the universe lift of the multiplicative
  type tag of Fin r → PadicInt l, with its original product/inverse-limit topology.
  IntegerLattice r similarly uses Fin r → ℤ and its discrete topology. The tags simply
  translate additive group notation for the existing multiplicative action API.
* The specified iota: latticeFunction is exactly coordinatewise integer cast, and
  latticeInclusion bundles this actual function as a continuous group homomorphism.
  No merely dense homomorphism or arbitrary generator list is substituted.
* Coefficient ring: coefficientRing uses continuousMapRingObjOfUniverse,
  continuousMapRingObjOfUniverseMonObj and its recorded commutativity theorem. The
  underlying sheaf is continuousMapRingSheafOfUniverse with sections C(S,F).
* V: Type v, AddCommGroup, Module E, FiniteDimensional E, TopologicalSpace,
  IsModuleTopology E. The joint action hρ is continuous on AdicLattice l r × V and
  ρ is a monoid homomorphism to E-linear equivalences. No semisimplicity or unipotence
  assumption is present.
* V_F: ScalarSpace E F V is the actual algebraic tensor product, equipped with
  moduleTopology F, equal to the finite-product norm topology. Realization specifies
  every section as C(S,F tensor_E V), every precomposition restriction, scalar
  multiplication and pointwise coefficientScalarExtension action. The section lifts
  only implement universe conventions. It works for both E and Ω; Ω is never completed.
  realization_exists has a complete construction proof in its docstring. Realizations
  are determined up to the unique isomorphism respecting these displayed section maps;
  their choice is not a choice of uncharacterized data.
* The action category is the existing CondensedAction.ActionModule, reexported as
  CondensedBar.Equivariant. No copied group-action category is introduced. Its fixed
  sections are the existing CondensedAction.FixedAll, quantifying over all base changes.
* Invariants use the existing Invariants specification: its inclusion is sectionwise
  injective, has exactly FixedAll image, and normalizes both adjunction transposes.
  actionAbelian supplies only proof properties of the fixed existing additive category.
* Ordinary RΓ is derivedInvariants: Mathlib totalRightDerived applied to the complex
  invariant functor and the quasi-isomorphism localization. HasDerivedCategory binders
  specify the morphism universe u+2; they do not impose a mathematical restriction.
* Restriction uses exactly CondensedAction.inflate. invariantRestriction is the unique
  factorization of the G-invariant inclusion through the H-invariant inclusion.
  restrictionUnitComponent maps this actual inclusion and follows the right-derived
  unit. derivedRestriction is rightDerivedDesc applied to that comparison. Thus b is
  the specified canonical map. moduleRestriction inserts only the existing exact
  restriction/single-complex identification on the target.
* Isomorphism: denseLatticeDerivedInvariantsComparison asserts IsIso of this very arrow
  for E and for Ω separately, in DerivedCategory of the corresponding internal modules.
  It asserts an isomorphism of derived objects, not merely cohomology isomorphisms.
* Degree zero: zeroIso is induced by the actual derived augmentation unit.
  moduleRestriction_zero identifies H⁰(b) with invariantRestriction under those
  normalized isomorphisms. realization_fixedSections proves precisely that L-fixed
  and D-fixed sections are the same submodule after every base change. The latter
  invariantRestriction is therefore identity on this common submodule; these two
  declarations together render the exact degree-zero clause without choosing an
  arbitrary identification.
* Naturality: realizationMap_existsUnique and realizationMap give the uniquely specified
  pointwise scalar-extended morphism induced by any equivariant E-linear f. Finite
  dimensionality and the module topologies imply continuity, so this covers exactly
  the node's continuous equivariant maps. moduleRestriction_naturality is the exact
  naturality square for this morphism (and indeed any internal equivariant morphism).
* Coefficients: coefficientRingMap is the recorded continuous-map postcomposition by
  algebraMap E Ω, with continuous_subtype_val. ExactScalar uses the existing ScalarAction
  underlying-module/action normalization. ScalarCompatibility specifies the ordinary
  invariant-inclusion square and, on every complex, the derived-unit square, fixing
  its derived comparison. coefficientMap derives the actual equivariant f and composes
  this normalized comparison. realizationCoefficientMap_existsUnique fixes f sectionwise
  by a tensor v maps to φ(a) tensor v, which under E tensor_E V = V is v maps to 1 tensor v.
  denseLatticeDerivedInvariantsComparison_coefficients states exactly the square
  c_D after b_E equals scalar restriction of b_Ω after c_L in D(Mod_C_E).
* Rank zero: both Fin 0 products and both universe lifts are singleton groups.
  trivialIso identifies their derived invariants with the same original module [0]
  using the actual invariant inclusion and derived unit. moduleRestriction_trivial
  says b followed by that target identification equals the source identification,
  exactly identity on V_F[0]. This applies directly to latticeInclusion l 0.

Dependency declarations read and used:

* Sheaf.Topology.ContinuousMapCondensedRing:
  Profinite.continuousMapRingSheafOfUniverse, continuousMapRingObjOfUniverse,
  continuousMapRingObjOfUniverseMonObj, isCommMonObj_continuousMapRingObjOfUniverse.
* Sheaf.Topology.ContinuousMapCondensedRingMap:
  Profinite.continuousMapRingSheafMapOfUniverse, continuousMapRingObjMapOfUniverse,
  isMonHom_continuousMapRingObjMapOfUniverse.
* Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod and Mod.comap.
* Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and HasDerivedCategory.
* Sheaf.CategoryTheory.CondensedActionModule:
  Profinite.CondensedAction.ActionModule, Invariants, FixedAll, inflate, sectionModule.
* Sheaf.CategoryTheory.CondensedEquivariantBarData:
  CategoryTheory.CondensedBar.Ring, Equivariant, Modules, ActionAbelian and ScalarAction.
* Sheaf.RepresentationTheory.LAdic: Representation.coefficientScalarExtension,
  IsEquivariant. The finite coefficient definition's usual topology is the same module
  topology used here; E has its norm induced from the norm-topological Ω.
* Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing.
* Proof imports: Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality,
  Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients,
  WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor, and
  Mathlib.Topology.Algebra.Module.FiniteDimension. The other recorded proof nodes have
  no Lean declaration in the current node records and cannot be imported yet.

The newly cited statement dependencies are already landed nodes exposing the exact action,
coefficient-extension and scalar-normalization declarations used by the statement. No new
node or dependency repair is delivered. No existing dependency declaration is replaced.

Edge cases read before writing: r=0, V=0, arbitrary finite dimension, trivial action,
nonsemisimple action, empty profinite test object, and incomplete Ω. IntegerLattice is
unconditionally discrete, rather than carrying the topology induced from L. The cohomology
is ordinary internal condensed-module derived invariants, not discrete Rep cohomology or
solid coefficients. Site/group universe u and vector-space universe v are explicit and
independent; a finite basis provides a small carrier for the realized finite-dimensional
module even when V lives in a larger universe. Definitions contain actual constructions or
choices determined by the inclusion/section/derived universal properties; no unconstrained
Nonempty isomorphism or arbitrary map replaces b or a coefficient map.

Searches actually run:

* msearch.py leanfinder: "Restriction of ordinary derived invariants of continuous finite
  dimensional ell adic condensed representations from Z_ell^r to the dense lattice Z^r".
  Eight hits, including Condensed.profiniteFree, Condensed.profiniteSolid,
  CondensedMod.LocallyConstant.functor, LightCondMod.LocallyConstant.functor and
  LocallyConstant.freeOfProfinite; none states this internal all-continuous comparison.
* msearch.py loogle: '"Condensed", "invariants"': zero hits.
* msearch.py grep: '(dense|PadicInt).*(cohomology|invariants)|(cohomology|invariants).*(dense|PadicInt)':
  zero hits in Mathlib.
* rg of lean/WeilConjectures and lean/Sheaf for denseLattice, dense_lattice and the item
  id: no exact declaration. Searches for derivedRestriction and CondensedAction locate
  the existing action/bar framework and unrelated ringed-site restrictions, read above.
* The current blueprint source was read in full: main-20261015 direct-image stability,
  paragraph (3). It delegates the open-immersion coefficient case to
  sk-prop-open-coefficients. The DAG honestly labels this further analytic expansion
  agent-formulated, with its exact all-continuous reference WANTED; this delivery
  preserves that provenance and does not claim an external proof.

The preserved sandbox contained only old briefing files, not a previous returned Lean
packet. The earlier stale-assignment message concerned a reviewed split; current live
node has a stage-1 NP split and no lean record. This delivery does not re-split the node.

Validation: every probe and delivered module uses module mode and scompile.py against the
live published library. The complete module with all required proof imports compiled
without errors or warnings, in 54.1 s for the sandbox check and 51.2 s for module mode.
Irreducibility attributes prevent unnecessary unfolding of the characterized scalar and
realization choices. The prescribed dry run and delivery perform their own server checks. No global build, direct Git mutation or live source edit was run.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
