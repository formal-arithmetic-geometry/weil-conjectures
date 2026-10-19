## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleAffineLineEndomorphismRigidity`
states `AlgebraicGeometry.Scheme.proEtale_a1_pullback_endomorphism_rigidity`.
The sole theorem has proof `sorry`. The accompanying definition
`AlgebraicGeometry.Scheme.proEtaleAffineLineUnitPullbackIso` has real data:
the inverse of the published pullback composition isomorphism, followed by
transport along Mathlib's section equation and the published identity-pullback
isomorphism. No construction, hypothesis or conclusion of the node is changed.
No new node or dependency repair is needed.

Clause-by-clause correspondence:

- Any scheme S: `(S : Scheme.{u})`, with no scheme-property instances or
  assumptions on the structure morphism.
- Finite commutative coefficient ring: `(Λ : Type u) [CommRing Λ] [Finite Λ]`.
  Coefficients in module sections are `ULift.{u+1,u} Λ`, as in the recorded
  constant-ring definition. This is the existing universe convention, not a
  coefficient extension. All finite coefficient rings can be represented in
  this bound. No field, nonzero-ring, Noetherian or characteristic condition
  is imposed.
- X = A1_S: `AffineSpace (ULift.{u} (Fin 1)) S`, exactly the coordinate type
  specified by the Mathlib match of `def-sbc-affine-space` at n = 1.
- Projection p: `AffineSpace (ULift.{u} (Fin 1)) S ↘ S`, Mathlib's first
  projection from the defining pullback.
- Unit section e: `AffineSpace.homOfVector (𝟙 S)
  (fun _ : ULift.{u} (Fin 1) ↦ 1)`. Its coordinate is the global section one.
  `AffineSpace.homOfVector_over` supplies e ≫ p = id in the actual comparison
  definition; this equation is not an extra theorem hypothesis.
- Small pro-etale sites: all categories and pullbacks use `Scheme.ProEt`
  and `ProEt.topology` through the recorded intrinsic coefficient API.
  Objects have universe u+1 and morphisms u; no equality of these universes
  is imposed, and the site is not replaced by a big site or an etale site.
- Modules over Λ_S: `M : proEtaleRingModules S (proEtaleConstantRing S Λ)`.
  These are intrinsic `SheafOfModules` over the sheafification of the
  constant commutative ring, forgetting commutativity to RingCat.
- Ordinary fixed-coefficient inverse images p*, e*: `sfIntrinsicPullback Λ`
  applied to those exact scheme maps. This is the ordinary inverse image
  reexported by the recorded `SfIntrinsicRealizationTransport` module,
  transported through the published canonical constant-ring realization.
  No derived category operation appears in the theorem.
- Local constancy: `hM : IsLocallyConstantProEtaleModuleSheaf S Λ M`.
  This is the original intrinsic predicate publicly reexported by the
  recorded `ProEtaleFixedModuleLocalConstancy` module through
  `ProEtaleLocallyConstantSheaf`. It specifies a pro-etale trivializing
  cover with module-sheaf isomorphisms and variable, arbitrary module
  models. The fixed-module predicate of the same recorded module is
  intended for the equivalent ModuleCat-valued presentation; it is not
  substituted for the intrinsic predicate on a different object type.
- Every geometric stalk is a finite Λ-module: `hfinite` quantifies over
  every bounded algebraically closed field Ω and every `Spec Ω ⟶ S`,
  asserting `Finite ((finiteCoefficientModuleStalkFunctor y Λ).obj M)`.
  This is the recorded stalk functor, using the pointed-neighbourhood
  module colimit and restriction along the constant-ring germ. Finiteness
  is finiteness of the underlying set, as in the node and its lisse-origin
  dependency; it does not mean free or merely finitely generated.
- Endomorphism h: its source and target are both the actual object
  `(sfIntrinsicPullback Λ p).obj M`.
- Normalization e*h = id_M: `he` says `e*.map h ≫ alpha_M = alpha_M`,
  where `alpha` is `proEtaleAffineLineUnitPullbackIso S Λ`. This is exactly
  `alpha_M.inv ≫ e*.map h ≫ alpha_M.hom = id_M`, after cancellation of
  the canonical isomorphism. The target M is fixed by the identity
  functor. No arbitrary isomorphism is quantified or chosen.
- Conclusion: `h = 𝟙 ((sfIntrinsicPullback Λ p).obj M)`.
- Final absence of restrictions on S: no separatedness, finite-type,
  quasi-compactness, reducedness, connectedness, nonemptiness or base field
  appears in the signature.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and Hom.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its `over`
  instance, `homOfVector`, and `homOfVector_over`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`, whose body records the same site and
  constant-ring coefficient category. The derived abbreviation itself
  is not applied: this statement is in the underlying module category.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the
  transparent abbreviation of Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction` and the reexported
  `sfIntrinsicPullback`, `sfIntrinsicPullbackComp`, `sfIntrinsicPullbackId`;
  the latter constructions are in `ProEtaleIntrinsicFiniteOperations`.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`: the reexported
  `IsLocallyConstantProEtaleModuleSheaf`, originally defined in
  `Sheaf.Paper.ProEtaleLocallyConstantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`:
  `finiteCoefficientModuleStalkFunctor`, using the recorded geometric
  module-colimit construction. Its object is the underlying stalk in
  the hypothesis, with the actual constant scalar action.

All stated proof dependencies are imported, including lisse origin,
finite-level comparison, pullback coherence, connected-fibre section
compatibility, etale inverse-image restriction and composition, ordinary
etale operations, polynomial domains and spectrum closure. Their imports
are non-public when used only for the proof. The node
`lem-pe-constant-left-module-inverse-image` currently has no recorded Lean
module; its role is explained in the proof docstring, and there is no
module to import. It is only a proof dependency, not needed to type this
statement. No dependency or replacement assertion for it is invented.

Edge cases checked before writing:

- Empty S is allowed: no points are required, the stalk condition is
  vacuous, and module-sheaf endomorphisms on the empty site are unique.
- Disconnected S and infinitely many components are allowed: local
  constancy does not require one global constant model or constant rank.
- Nonreduced bases, arbitrary characteristic and non-quasi-compact bases
  remain in the signature. The geometric-fibre argument concerns the
  polynomial ring over a geometric residue field, not reducedness of S.
- The zero module and the zero coefficient ring are allowed; there is
  no `Nontrivial` hypothesis. All relevant maps are then unique.
- Finite modules need not be free; nontrivial monodromy is allowed since
  M is locally constant rather than globally constant.
- The only coordinate index is ULift (Fin 1), inhabited in every u.
  No point or cover-index universe is independently smaller than S.

Searches (performed anew for this delivery):

- `msearch.py ... leanfinder`: "An endomorphism of a finite locally
  constant pro-etale module sheaf pulled back to the affine line over an
  arbitrary scheme is identity if its restriction at t equals one is
  identity". Eight hits, including `AffineSpace.reindex_id`,
  `Scheme.Modules.pullbackId`, `Scheme.Pullback.t_id`,
  `Scheme.Modules.restrictFunctorId`, `AffineSpace.map_id`; none states
  finite pro-etale local-system endomorphism rigidity.
- `msearch.py ... leansearch`: "Endomorphisms of finite locally constant
  module sheaves pulled back to an affine line are determined by their
  restriction to a section". Eight hits, including `LocallyConstant.comapₗ`,
  `Scheme.Modules.restrictStalkNatIso`, `Module.End` and condensed locally
  constant module functors; none is this statement.
- `msearch.py ... loogle`: `"AffineSpace", "LocallyConstant"`: zero hits.
- `msearch.py ... grep`:
  `proetale.*(endomorphism|rigidity)|AffineSpace.*LocallyConstant`: zero hits.
- `rg` of WeilConjectures and `lean/Sheaf` for the item id and affine-line
  endomorphism/rigidity names found only the distinct finite-type purity
  rigidity module `PurLisseMorphismRigidity`. That node assumes a finite-type
  base and does not state this arbitrary-base assertion. No exact match.
- `rg` of Mathlib, WeilConjectures, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the new declaration names: no matches.

Sources opened: `etale-cohomology.tex`, lemma-sections-upstairs (Tag 0A3H),
including the final connected-geometric-fibre compatibility argument, and
`proetale.tex`, lemma-compare-locally-constant (Tag 099Y). The proof
in the docstring follows all eight steps of the supplied DAG proof and
keeps their ordinary, module-linear unit/composition identifications.
No statement fault or STATEMENT-DISPUTED issue was found.

Validation: `scompile.py N8 lem-pur-a1-pullback-endomorphism-rigidity`
compiled the delivered file successfully in both the sandbox probe and
library-module check (12.3 s and 23.9 s), with no errors or warnings.
The theorem is intentionally postponed, as required for stage 2.

The dispatcher brief requires direct delivery without starting other
agents. The maintainer's independent delivery review is the second
reading; no independent-worker review is claimed here.

The first delivery preflight requested that lean.statement omit the terminating
`:=`; the metadata was repaired to its exact signature convention.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
