## Worker report

The module `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison` states
`CategoryTheory.SheafPolynomialCotangent.sheaf_polynomial_cotangent_comparison`.
Its conclusion is `Nonempty (Comparison f)`. The record includes all presentation
models, canonical chain maps, derived comparison isomorphisms, their coherence,
and the normalized cokernel isomorphisms. No proof is supplied at stage 2.

Source read: `literature/stacks-project/sites-modules.tex`, label
`lemma-NL-up-to-qis`, Tag 08TY, including the image-presheaf claim and its local
injectivity and surjectivity arguments; label `lemma-differential-seq`, Tag 08TS,
including the formula and the image-presheaf proof of exactness. The five proof
steps of the accepted DAG split are reproduced in the main theorem's docstring.
The item is not a blueprint unit's own statement and needs no statement correction.

Hypothesis and clause correspondence:

- Small site: explicit `universe u`, `{C : Type u} [SmallCategory C]`, and the
  theorem's `(J : Precoverage C) (_hJ : J.IsSiteForCoverings)`. All sheaves use
  `J.toGrothendieck`. This uses the recorded covering-site axiom interface without
  adding the existence of any noncovering pullbacks. The single bound is the
  node's chosen universe of small site objects, arrows and values.
- Sheaves of commutative rings and their map: `(A B : Sheaf J.toGrothendieck
  CommRingCat.{u}) (f : A ⟶ B)`. No ring, finiteness, or nonzero hypothesis is added.
- Module sheaves are the recorded `ringedSiteModules (siteModuleRings B)`.
  `derived B` and `localization B` explicitly use Mathlib `DerivedCategory` and
  `DerivedCategory.Q` with `HasDerivedCategory.standard`. No assumption about
  a special derived localization or extra size equality is imposed.
- An arbitrary sheaf of sets and map to the underlying sheaf of `B` are
  `Presentation.generators` and `Presentation.values`. `sets` just applies the
  forgetful functor, without a lift or a new sheaf construction.
- `polynomials A E` has exactly sections `MvPolynomial (E(U)) (A(U))`; its
  restrictions apply `A`'s restriction to coefficients and `E`'s restriction to
  variable labels. `polynomialSheaf A E` is its actual ring sheafification.
  `base` is the coefficient inclusion followed by the sheafification unit.
- `evaluationPresheaf` is `MvPolynomial.eval₂Hom` with coefficients from `f` and
  variables from `values`; `evaluation` is its unique lift along sheafification.
  `Presentation.surjective` is `Presheaf.IsLocallySurjective` on this sheaf map.
  This is sheaf surjectivity, not sectionwise surjectivity and not surjectivity
  of the map of generating sets.
- `kernelIdeal P` is the recorded ideal-sheaf structure with sections exactly
  `RingHom.ker` of evaluation. Its actual restriction/local membership axioms
  are the two clauses of the named theorem `kernel_ideal_axioms`.
- `LocallyInKernelSquare` requires a covering sieve on which the restricted
  section lies in the square of the sectionwise evaluation-kernel ideal.
  Ideal powers mean finite sums of products. This is exactly the *sheaf* square,
  and does not confuse it with the possibly smaller presheaf square on `U`.
- The conormal quotient is `(Model P).complex.X (-1)` with its canonical
  `quotient` map from `(kernelIdeal P).module`, linear over `A[E]` after restriction
  of scalars. `quotient_surjective` makes it locally surjective, and
  `quotient_kernel` says its kernel is exactly the locally generated ideal
  square. In an abelian sheaf category these two conditions characterize
  `J/J²` with its quotient map up to unique compatible isomorphism. There is
  no arbitrary module assumption and no choice from mere uncharacterized existence.
- `differentialTerm P` is the existing sheaf change of rings of the existing
  `SheafDifferentials.omega (base A E)` along evaluation. It is precisely
  `Ω_{A[E]/A} ⊗_{A[E]} B`; `tensorD P U b p` is `b ⊗ dp`, using the symmetry of
  the source's displayed factor order.
- `Model.degreeZero` identifies degree zero with that actual differential term.
  `supported` requires zero in every degree except -1 and 0.
  `Model.differential_formula` sends the quotient class of each kernel section
  to `1 ⊗ dj`. These normalizations specify exactly the node's two-term complex,
  allowing its unavoidable categorical identifications instead of arbitrary data.
- `canonical f` is `E = sets B`, `values = identity`; its surjectivity theorem
  uses the local polynomial `X b`. Thus `models (canonical f)` is exactly NL,
  rather than an independent cotangent object assumed in a hypothesis.
- For each generator map `v` with `v ≫ values' = values`, `polynomialMap` is
  the sheafification of actual polynomial variable renaming with coefficients
  unchanged. `GeneratorMap.chainMap` is a chain map of the displayed models;
  `conormal_formula` specifies it on every quotient class and
  `differential_formula` sends `b ⊗ dp` to `b ⊗ d(P(v)p)`. The quantified target
  kernel representative exists since evaluation commutes with maps over `B`.
  These generators locally generate both terms, so these conditions characterize
  the canonical map. They are not arbitrary comparison morphisms.
- `Comparison.quasiIso` says each such canonical chain map is a quasi-isomorphism.
  `lambda P` is an actual isomorphism in the recorded derived category to the
  identity-generator model; `lambda_hom` identifies its forward map with the
  localization of the canonical generator map `values : E → B`.
- `Comparison.naturality` is precisely `Q(K(v)) ≫ lambda_E'.hom = lambda_E.hom`.
  `identity` and `composition` give the actual chain-map identity and composition
  laws for all presentations and all maps over `B`.
- `cokernelIso P` identifies the cokernel of `K_E.d (-1) 0` with the existing
  `SheafDifferentials.omega f`. `cokernel_formula` specifies its composite with
  the cokernel projection on every local tensor `b ⊗ dp` as `b • d(ev(p))`.
  Via `degreeZero` this is exactly the node's canonical map from `F_E`, so the
  conclusion includes its induced isomorphism, not merely an abstract isomorphism.

The records describe the canonical quotient/complex/map constructions through
complete local normalizations. The main existential theorem asserts their
existence and all comparison properties together. No object is defined by
`Classical.choose` or `Nonempty.some` of this theorem. In particular the
conormal module is not chosen from an existence statement that leaves it
undetermined. The only postponed theorems are `canonical_surjective`,
`kernel_ideal_axioms`, and the main theorem, all listed in `lean.declarations`
and documented with the corresponding argument in the item's proof.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` and Mathlib's `toGrothendieck`.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no
  declaration: explicit `u` and the standard derived localization implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  which is transparently Mathlib `SheafOfModules`, with its abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, `QuasiIso`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`, including the adjunction's `homEquiv`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `C`, `X`,
  `eval₂Hom` and the existing variable-renaming algebra map.
- `Sheaf.Paper.RingedSiteIdeal`: `RingedSiteIdeal`, `.module`, and `siteModuleRings`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`, and the universal
  `linearMapEquivDerivation`, used through the already constructed differential
  presheaf/sheaf API rather than copied.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` publicly imports
  the existing `SheafOfModules.changeOfRingsOfUniverses` and its presheaf, from
  `TensorProductOfUniverses`; the section tensor and sheafification are unchanged.
- The new definition node `def-sfb-sheaf-differentials` binds the already landed
  `Sheaf.CategoryTheory.Sites.InverseImageDifferentials` definitions
  `CategoryTheory.SheafDifferentials.ring`, `.sets`, `.moduleSets`, `.omega`,
  `.derivation`, and `.d` with `existing: true`. The construction and signatures
  were read locally and checked against the current server source. The item cites
  this definition node, rather than the inverse-image comparison theorem.
- The stated proof dependencies are imported, including image-presheaf
  sheafification, sheafified differentials, sheafified tensor, local sections,
  polynomial-presentation homotopy equivalence, and locally dense cotangent H1.
  The remaining mathlib leaves are available through those imports.

Edge cases checked before writing:

- Empty generators are allowed: coefficient evaluation need only be sheaf-surjective;
  this includes sheaf quotient maps `A → B` and is not excluded by a nonempty binder.
- Identity generators always work even when sections do not lift along an arbitrary
  presentation. `X b` proves exactly the separate canonical surjectivity helper.
- Zero rings and zero target sheaves are allowed; kernels and tensor terms have their
  usual values, and all normalizations still type without `Nontrivial`.
- Empty sites and empty covering sieves are allowed. The local square predicate uses
  actual covering-sieve membership and remains correct for locally zero sections.
- Identity-cover sites reduce the sheaf quotient and sheaf-surjectivity clauses to
  the usual ring polynomial-presentation calculation. On sites with nontrivial
  covers, the local square and surjectivity clauses do not impose global lifts.
- Arbitrary infinite generator sheaves and arbitrary characteristics are retained.
  No finite generation, freeness, characteristic-zero, or enough-points hypothesis.
- `degreeZero` and `supported` account for all integer degrees, including positive
  degrees and degrees below -1; no truncation clause is omitted.

Searches run (all through the prescribed msearch wrapper where applicable):

1. LeanFinder: `On a site, polynomial presentations of a sheaf of algebras give
   quasi-isomorphic naive cotangent complexes` — eight ring-level hits, including
   extension cotangent maps and polynomial presentation lemmas; no sheaf comparison.
2. Loogle: `KaehlerDifferential, MvPolynomial` — twelve hits on polynomial differential
   bases and ring-level extension cotangent maps; none states this sheaf comparison.
3. Mathlib grep: `Cotangent|cotangent` in `Algebra/Category` — zero hits.
4. LeanSearch: `naive cotangent complex of polynomial presentation of sheaf of rings`
   — eight hits, including module-sheaf presentations, ideal cotangent and extension
   H1; none states the target.
5. `rg` of `lean/WeilConjectures` for cotangent/polynomial sheaf terms and the exact
   item id — no matching comparison. The ring and unrelated polynomial declarations
   do not state the site theorem.
6. `rg` of `lean/Sheaf` for cotangent, differentials, conormal and polynomial sheaves
   found `LocallyDenseCotangentH1`, `SheafifiedDifferentialsCokernel`,
   `Sites/InverseImageDifferentials`, the topological `SheafCotangentComparison`,
   and ring-level `CotangentSheafModel`/`NaiveCotangentComparison`. Their signatures
   were read. The topological construction is restricted to `TopCat` and ring-valued
   generators; the ring presentation-site model has another site and notion. Neither
   supplies this arbitrary-site arbitrary-set-sheaf comparison. The generic existing
   omega, tensor and ideal constructions are reused instead of duplicated.

No STATEMENT-DISPUTED flag, source error, statement correction or dependency-module
repair. The item adds the new differential-sheaf definition node to `stmt_deps`.
Its statement, proof and proof dependencies are unchanged.

## Second reading by Q150

A separate rereading pass checked the node's full statement against each record
field and the main theorem after drafting. This is the dispatcher's worker's own
second pass; the maintainer performs the independent review on delivery.

The pass checked that the evaluation hypothesis is local sheaf surjectivity, that
`quotient_kernel` uses the *local* ideal square, that the two exceptional degrees
are exactly -1 and 0, that the tensor is actual sheaf scalar extension, and that
lambda's hom is the localized canonical map to the identity-generator presentation.
It also checked the orientation of naturality and composition, and that the cokernel
isomorphism has the evaluation formula rather than an arbitrary forward arrow.
The initial elaboration checks required explicit universe parameters on the
existing omega and scalar-extension APIs, the ring-colimit/sheafification imports,
and explicit polynomial ring-hom extensionality. These changes affect elaboration,
not the mathematical hypotheses or conclusions. The final main binder uses the
recorded covering-site axiom interface. No mathematical mismatch was found.

Validation: prescribed `scompile.py` passed both sandbox and named-library checks
with no errors or non-sorry warnings. `deliver2.py --no-push` printed
`OK (dry run): commit 5493a2a5c9d passes the preflight and compiles; nothing pushed`.


## New nodes

`def-sfb-sheaf-differentials` is a definition node in the item's chapter and unit,
binding the existing construction in `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`.
It introduces no Lean module. Its three statement dependencies are the existing
sheafification, ring Kähler differential, and module-sheaf category definitions.
Tag 08TP (`lemma-differentials-sheafify`) and the preceding
`definition-module-differentials` were reread in `sites-modules.tex`.

For each hypothesis and clause of the new node: `{C : Type uC} [Category.{vC} C]`
and `[EssentiallySmall.{w} C]` give its general essentially small category;
`{J : GrothendieckTopology C}` is its topology; `{A B : Sheaf J CommRingCat.{w}}`
and `(φ : A ⟶ B)` give exactly its ring sheaves and ring map. `omega φ` is
`PresheafOfModules.sheafification` applied to `relativeDifferentials' φ.hom`,
whose objects and restrictions were read in Mathlib's `Differentials/Presheaf.lean`.
`derivation φ` postcomposes `derivation' φ.hom` with the same sheafification
adjunction unit. `d φ` gives the section formula on the lifted underlying sheaves;
`ring`, `sets`, and `moduleSets` are the stated forgetful constructions.
These are actual definitions, independent of the inverse-image comparison theorem.
They also work for zero rings and empty sites; no nontriviality, characteristic,
finite generation, or equality of site object and morphism universes is added.

Fresh searches on 2026-10-24 used the prescribed wrapper:
- LeanSearch: `sheafification of sectionwise Kahler differentials with universal derivation`:
  eight hits, including `relativeDifferentials'`, `isUniversal'`, and generic `sheafify`.
- LeanFinder: `sheaf of relative Kahler differentials as sheafified sectionwise differentials with universal derivation`:
  eight hits on the sectionwise differential presheaf and its derivation.
- Mathlib grep: `relativeDifferentials|SheafDifferentials|KaehlerDifferential`,
  subdirectory `Algebra/Category/ModuleCat`: ten hits in differential Basic/Presheaf.
- Local `rg` in `lean/WeilConjectures` found scheme-specific relative-differential
  APIs; `rg` in `lean/Sheaf` found the exact generic definitions reused here.
- DAG searches for sheafified sectionwise differentials and the declaration names
  found theorem records and consumers, but no definition node owning these definitions.
  `tools/blueprint_refs.py search 'sheaf differentials'` returned zero blueprint nodes;
  `ancestor` returned `None`, retained in the new node's blueprint ancestry.
The new node records these results in `mathlib_searches`.

## Repair of return on 4db191f6a9ca

H2: replaced the added theorem dependency
`lem-trf-topos-inverse-image-differentials` by the new definition node
`def-sfb-sheaf-differentials`. Its `lean` has `existing: true` on the requested
module and all six requested declarations. The existing main Lean module is
unchanged. Comparing the retained packet with current main showed only `lean`
and `stmt_deps` differ on the item; no accepted split or statement is reopened.
The initial saved-packet dry run passed at `fad94b0f55b`; the substantive ownership
repair is included even though that mechanical gate did not detect the H2 issue.

The second reading by Q150 rechecked the six existing definition bodies and the
new node clause by clause against 08TP. The constructions use sheafification and
its unit directly, rather than choosing from an inverse-image theorem. The item
still uses exactly these definitions for its differential term and cokernel.

The repaired-packet preflight requested the schema field `import_flags` and the
normalized signature beginning `def omega`. Added the empty flags field and
recorded the signature in that format; no mathematical content changed.

Repair validation: `scompile.py` passed the unchanged main Lean module in both
sandbox and library modes. The repaired packet passed `deliver2.py --no-push`:
`OK (dry run): commit 2a3751a1cae passes the preflight and compiles; nothing pushed`.
The existing-definition check also compiled the six reused declarations.
