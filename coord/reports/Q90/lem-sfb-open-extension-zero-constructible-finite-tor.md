## Worker report

The module `Sheaf.Paper.OpenExtensionConstructibleFiniteTor` states
`AlgebraicGeometry.ProEtale.CondensedRing.openExtension_constructible_finiteTor`.
Its only postponed proof is the whole `sorry` proof of this theorem, matching
lem-sfb-open-extension-zero-constructible-finite-tor. No definitions, new nodes,
dependency repairs, or statement corrections are introduced. The source statement
and all other original node fields are unchanged.

Hypothesis and clause correspondence:

- The fixed prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The field and positive characteristic different from ell are `(k : Type u)
  [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. A field's positive
  characteristic is prime, so the first Fact expresses the specified p > 0.
- Separated finite-type k-schemes are `U X : Over (Spec (.of k))`, with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on both structure maps.
  Finite type is locally finite type together with quasi-compactness.
- The k-morphism is `j : U ⟶ X` in Over, and open immersion is
  `[IsOpenImmersion j.left]`; no extra quasi-compactness hypothesis is imposed on j.
- Arbitrary commutative condensed coefficients are `Λ : Sheaf
  (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`.
  This is the unbundled version of the dependency's `Profinite.CondensedRing`.
  No topological presentation, admissibility, completeness, finite-coefficient,
  Noetherian coefficient, or finiteness-coefficient class is assumed.
- The pulled-back ring object is precisely `condensedRingObj Λ U.left` or
  `condensedRingObj Λ X.left`, through the dependency definitions.
- `A : ConstantModelConstructibleFiniteTor Λ U.left` is the full subcategory of
  ordinary unbounded derived internal modules, with the property
  `constantModelBoundedConstructible Λ U.left ⊓ finiteTorAmplitude _`.
  `A.obj` is its underlying derived object. The bounded predicate uses
  `IsConstantModelConstructible`, hence finite stratifications with
  `HasFiniteConstantLocalModel`, rather than the general local-presentation notion.
- Exact termwise open extension is
  `(openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj` everywhere.
  This is D(j_!), not a total derivation of a compactification's underived composite.
- The four arbitrary integer endpoints are `(m n a b : ℤ)`. The node's Tor
  endpoints u,v are renamed a,b to avoid the Lean universe name u.
- The given cohomological interval is
  `hcoh : DerivedCategory.homologyConcentratedIn m n A.obj`.
- The given Tor interval is `htor : DerivedCategory.torAmplitudeIn _ a b A.obj`.
  This predicate quantifies over every module sheaf N, placed in degree zero by
  `DerivedCategory.singleFunctor _ 0`, and uses the ordinary relative derived
  tensor, definitionally the monoidal tensor underlying `derivedTensor Λ U.left`.
- The first conclusion is membership of the actual output in
  `constantModelBoundedConstructible Λ X.left ⊓ finiteTorAmplitude _`, exactly the
  object property defining Dctf(X,Λ), without choosing a replacement output object.
- The second conclusion is `homologyConcentratedIn m n` of this output, preserving
  the supplied cohomological interval verbatim.
- The third conclusion is `torAmplitudeIn _ a b` of this output, preserving the
  independently supplied Tor interval verbatim.
- The fourth conclusion is `boundedConstructible (condensedRingObj Λ X.left)` of
  this output. This is the general ring-object predicate, using
  `IsConstructibleModuleObject` and local finite presentation on finite strata.
  It does not replace the constant-model predicate in the first conclusion.

Dependency declarations read and used (each listed statement module is publicly imported):

- sk-def-sfb-dc-setting: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; the setting
  is rendered by explicit Over, field and structure-map binders as its record prescribes.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- sk-def-sfb-condensed-ring: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`, transparently `Mon` of profinite-site abelian sheaves;
  its unbundled underlying-object convention is used.
- sk-def-sfb-pulled-back-coefficients: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`, publicly
  available through the statement dependencies.
- sk-def-sfb-derived-categories: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, and its
  existing `DerivedCategory` convention; no replacement derived category is defined.
- sk-def-sfb-derived-tensor-hom: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` and publicly reexported
  `derivedTensor`; `DerivedCategory.torAmplitudeIn` and `finiteTorAmplitude` are
  from `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`, publicly
  reexported by CondensedConstantConstructibility.
- sk-def-sfb-module-derived-lower-shriek: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `rightDerivedLowerShriekOfCompactification` uses exactly the same
  `openImmersionLowerShriek.mapDerivedCategory` factor as this statement. For an
  open immersion the statement directly names this exact termwise factor.
- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
- sk-def-sfb-bounded-constructible:
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`, publicly
  retaining `AlgebraicGeometry.ProEtale.boundedConstructible` from
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
  The discrete coefficient-sized specialization is not used; the recorded module
  explicitly reexports the general ring-object interface needed here.

Every recorded proof-dependency module is imported plainly unless already a public
statement import. Mathlib leaves use their recorded source modules, including affine
qcqs, finite-type Noetherianity and exact-functor homology. The unstated proof-only
node lem-sfb-noetherian-complementary-stratifications has no recorded module, so
there is none to import; its mathematical step is included in the proof docstring.
The docstring follows all seven proof steps, including actual old strata plus
reduced complement, retaining the scalar models, the one-way local-presentation
implication, and tensoring against arbitrary test sheaves.

Edge cases checked before writing and again after compilation:

- U empty and X empty: no nonempty-scheme or nonempty-stratification binder appears;
  termwise extension sends the zero sheaf to zero. The zero scalar module is allowed.
- Identity open immersion: the closed complement may be empty, and the same interval
  statements reduce to those supplied for A.
- Zero object and zero coefficient ring: no nontriviality binder excludes them.
- Singleton, disjoint, reversed or independently chosen integer intervals are allowed.
  The zero object satisfies all of them; no ordering or equality of intervals is added.
- Degree-zero test sheaves in Tor amplitude have no constructibility or finite-generation
  restriction. Ordinary relative tensor, rather than completed tensor, is used.
- A field of characteristic zero is excluded exactly as the node specifies; every
  positive characteristic different from ell is allowed.
- Schemes and fields live in arbitrary universe u, sheaves in the existing Ab.{u+1}
  convention. No identification of the site's object and morphism universes is imposed.

Searches for an exact existing statement:

- msearch.py leanfinder: "Open extension by zero preserves constant scalar model
  constructibility and each Tor amplitude interval for arbitrary condensed coefficients".
  Eight results concerned condensed constructions and shape-extension of complexes;
  none states this theorem. Exact names and query are in searches.jsonl.
- msearch.py loogle: `"openImmersionLowerShriek", "torAmplitudeIn"`: zero hits.
- msearch.py grep in Mathlib CategoryTheory:
  `openImmersionLowerShriek|ConstantModelConstructibleFiniteTor|torAmplitudeIn`: zero hits.
- msearch.py leansearch: "Extension by zero for open immersion preserves bounded
  constructible module complexes and specified Tor amplitude": eight hits on functions,
  complex embeddings and restriction, none on this statement.
- rg in both lean/WeilConjectures and lean/Sheaf for
  `ConstantModelConstructibleFiniteTor`, open-extension constructibility and Tor names:
  `constantModelConstructible_openImmersionLowerShriek` in
  Sheaf.Paper.OpenExtensionConstantModelConstructible is about module sheaves and
  extra stratification data; OpenExtensionFiniteTor is specialized to finite coefficient
  quotients; CtfStabilityDirectImages assumes admissible coefficients; the upstream
  boundedConstructible_openImmersionLowerShriek_obj only gives the general
  ring-object bounded conclusion. None states the complete arbitrary-coefficient,
  independent-interval theorem here.
- rg/grep of the node id in lean/WeilConjectures: no hits. The chosen declaration name
  and module name have no hits in either project root or dag/lean_names_upstream.json.

Validation: scompile.py compiled the module separately in sandbox mode (6.5 s)
and library mode (6.1 s), under the unchanged 60-second limit, with no diagnostics.
No global build or direct git command was run. No statement dispute was found.

## Second reading by Q90

This is a second pass by the same dispatched worker, not an independent-agent review:
the dispatch explicitly prohibits starting other agents, and the maintainer supplies
its own independent review of the delivery. I reopened the node and module together.
The four output conjuncts match Dctf membership, the cohomological interval, the Tor
interval and general ring-object bounded constructibility, respectively. The input
uses the recorded constant-model full subcategory, the exact same output object in
every conjunct, and independent integer endpoints. The Over binder supplies the
k-morphism condition without another chosen structure map. Prime positive
characteristic is equivalent to the field hypothesis p > 0; no coefficient class is
added. The report distinguishes the record's discrete bounded-constructible extension
from its reexported general predicate. No mismatch requiring a source correction or
new definition was found. The complete seven-step docstring is present, all variables
and the universe are explicitly bound, and the module has compiled cleanly.
