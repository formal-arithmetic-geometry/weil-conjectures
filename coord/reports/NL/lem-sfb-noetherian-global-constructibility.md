## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility` states
`AlgebraicGeometry.Scheme.etale_noetherian_global_constructibility` and
`AlgebraicGeometry.Scheme.proEtale_noetherian_global_constructibility`, both with
`sorry` proofs. They give the item's two equivalences separately, one for each small
site. The statement of the item is unchanged. The dependency module supplies the
coefficient-size extension of the already recorded affine-local pro-etale notion.
There are no new DAG nodes and no new postponed helper theorems.

Hypotheses and clauses, read against the node and both declarations:

- Scheme: `(X : Scheme.{u})` is the recorded Mathlib scheme, including its category
  of scheme morphisms. `[IsNoetherian X]` means locally Noetherian and quasi-compact.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` and
  `isNoetherian_iff_of_finite_iSup_eq_top` identify this exactly with the item's
  finite affine cover by spectra of Noetherian rings. No separatedness is added.
- Coefficients: `(R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]`
  permits an independent coefficient universe `v`; there is no `Finite R`,
  nonzero-ring, characteristic or invertibility assumption. For a smaller ring
  its usual universe lift places it in this universe without changing its modules.
- Site choice: the etale declaration uses `smallModelComparisonEtaleTopology`,
  and the pro-etale declaration uses `coefficientProEtaleModelTopology`. These are
  the published topologies induced by `AsSmall.down` from `X.smallEtaleTopology`
  and `Scheme.ProEt.topology X`, respectively. They are equivalent models of the
  entire original small sites, retaining objects and covering sieves; only the
  universe encoding of objects and morphisms changes. The original pro-etale site
  still has object universe `u+1` and morphism universe `u`.
- Sheaf: `F : ConstantCompletion.Mod (ConstantCompletion.constant T R)` unfolds
  to the existing `ringedSiteModules` / `SheafOfModules` over the constant sheaf
  of commutative rings, after forgetting commutativity. The name
  `ConstantCompletion.Mod` imposes no completion condition. Its ring argument
  here is the constant ring, not a completed ring or an inverse limit.
- Inverse-image restriction: `coefficientEtaleFixedPullback` and the dependency's
  `coefficientProEtaleFixedModulePullback` are actual left Kan extension and
  sheafification along scheme base change on those equivalent sites. Applied to
  `((coefficientModelFixedScalars _ R).obj F)`, these read the fixed-ring module
  inverse image, using the canonical identification of inverse-image constants.
  The scalar restriction retains the underlying abelian sheaf and its constant
  R-action; no arbitrary comparison map, sheaf, or left adjoint is assumed.
- Condition (i), etale: `IsCoefficientConstructibleEtaleModule X R F` is the
  recorded predicate from `def-pe-etale-constructible-module`. Its definition
  quantifies over **every** `U : X.Opens` with `IsAffineOpen U`, then over a finite
  `LocallyClosedStratification U.toScheme` with constructible parts, and tests
  local constant models of the pullback along `S.immersion a ≫ U.ι`.
- Condition (i), pro-etale:
  `IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X R F` is the
  repaired dependency predicate. It has exactly the same affine-open and
  immersed-stratification quantifiers, with the explicit finitely presented
  constant-module local models from the original predicate.
- Finite stratification in (i) and (ii): `LocallyClosedStratification` contains
  `n : ℕ`, `stratum : Fin n → Set X`, locally closed pairwise disjoint parts
  covering X, actual `domain` schemes, `immersion` maps, immersion properties,
  and equality of their images with the corresponding parts. Thus this is a
  finite scheme stratification, not just a partition of sets; it retains arbitrary
  scheme structures on strata. `Topology.IsConstructible (S.stratum a)` is
  the recorded retrocompact-open Boolean-algebra notion. The same condition in
  affine-local predicates is constructibility inside the affine open.
- Condition (ii): each right side begins `∃ S : LocallyClosedStratification X`
  and requires `∀ a, Topology.IsConstructible (S.stratum a)`. The pullback is
  now along `S.immersion a`, so a single global finite partition is required.
- Local constancy, etale: `IsCoefficientModelLocallyConstantFinite T R G`
  expands to `∀ V, ∃ S : Sieve V, S ∈ T V ∧ ...`; on every arrow `U ⟶ V`
  in S there exists `M : ModuleCat R` and a module-valued sheaf isomorphism
  `G.over U ≅ (constantSheaf (T.over U) (ModuleCat R)).obj M`.
- Local constancy, pro-etale: the same covering-sieve quantifiers and slice
  constant-sheaf isomorphism are written explicitly on the right side and in the
  repaired affine-local predicate. `Module.FinitePresentation R M` is imposed
  on the module chosen for each covering member. Quantification over all objects
  is the usual covering-local formulation: it implies a trivializing cover of
  the terminal object, and pulling that cover back gives the converse formulation.
- Finite presentation: pro-etale uses `Module.FinitePresentation R M` literally.
  The existing etale predicates use `Module.Finite R M`. Under the explicit
  `[IsNoetherianRing R]`, `Module.finitePresentation_of_finite` gives the former
  from the latter, and the `Module.FinitePresentation` instance gives the converse.
  Hence they say exactly the same thing here, with neither a weaker conclusion
  nor an extra assumption. In both cases M is chosen inside the quantifier over
  covering members and can vary; there is no `Finite M` or bounded rank condition.
- Equivalence: each declaration uses `↔`. Neither assumes affine-local
  constructibility as a binder, nor adds a hypothesis in one direction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-fg
  characterization; `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian`
  and the finite-affine-cover equivalences above.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, and `ofArrows_mem_smallEtaleTopology_iff`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: reexports the recorded
  `Scheme.ProEt` and `Scheme.ProEt.topology` site and constant-ring category.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`, extending the existing
  `Topology.Stratification` with schemes and immersions.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, `IsRetrocompact`.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `upperStarLowerStarAdjunction`; the
  coefficient-sized etale inverse image is the same Kan-extension/sheafification
  construction transported to the equivalent small model.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`: the recorded
  inverse-image module, publicly retaining `ProEtaleInverseImage` and its
  `proEtaleBaseChange`, `proEtaleConstantModulePullback`, and coefficient maps.
  Its finite-coefficient adjunct is not used as an extra hypothesis here.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`:
  `coefficientProEtaleSiteModel`, `coefficientProEtaleModelTopology`,
  `coefficientProEtaleModelBaseChange` and its continuity. These retain the
  canonical base-change functor for arbitrary coefficient size.
- `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`:
  `smallModelComparisonEtaleSite` and `smallModelComparisonEtaleTopology`.
- `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`:
  `coefficientModelFixedScalars`, `IsCoefficientModelLocallyConstantFinite`,
  `coefficientEtaleFixedPullback`, `IsCoefficientConstructibleEtaleModule`.
- `Sheaf.Paper.ConstantCompletionEquivalence`: transparent `constant` and `Mod`
  abbreviations, used solely for the ambient constant-ring module category.
- `Sheaf.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules`:
  `IsAffineLocallyConstructibleProEtaleModuleSheaf`, whose full source signature
  and explicit local-model docstring were read and are retained by the repair.

Proof-only imports include the recorded `ProEtaleToposFunctorialityInverseImage`,
`SiteInverseImageTensor`, upstream `EtaleStratificationLocalGluingCore`, upstream
`ConstructibleSheaf.Pullback`, and the Mathlib covering/base-change, finite-limit,
Noetherian-space, and Noetherian-scheme material. The upstream gluing source was
read with `scompile.py --source`: its currently published type uses
`Scheme.Stratification`. No duplicate side declaration of its theorem is imported.
The unstated proof nodes `lem-pe-constant-left-module-inverse-image` and
`lem-sfb-geometric-inverse-image-constant-module` have no recorded module to
import; both are named at their corresponding proof steps in each docstring.

Edge cases checked before stating:

- Empty X and empty affine opens: S.n can be zero, and every stratum/local-model
  quantifier over `Fin 0` is vacuous. No positive-stratum or nonempty-site binder.
- R = 0: commutative Noetherian zero rings and their zero modules are allowed.
- R = ℤ and M = ℤ: these are valid infinite underlying sets, so any finite-set
  formulation would be wrong; our models require only module finite presentation.
- Non-separated Noetherian schemes: no separatedness hypothesis and no use of
  affine intersections being affine. The proof uses quasi-separatedness derived
  from local Noetherianity.
- Non-reduced immersed strata: actual scheme immersions are retained. The proof
  uses actual refinement factorization maps, not only containment of images.
- Independent coefficient universe: `u` and `v` are explicitly bound; the old
  Type-u coefficient limitation is repaired, not turned into a hypothesis.
- Covers may be infinite; only the number of strata is finite, as in the node.

Searches for an existing statement, all executed for this item:

1. `msearch.py leanfinder`: "Affine-local constructibility of etale or proetale module
   sheaves on a Noetherian scheme is equivalent to a finite global locally closed
   constructible stratification". Eight hits: Noetherian affine-cover criteria,
   Noetherian spaces and constructible images, no sheaf equivalence.
2. `msearch.py loogle`: `"IsConstructible", "Sheaf"`. OK, zero hits.
3. `msearch.py grep`: `constructible.*sheaf|sheaf.*constructible|stratification`.
   OK, zero hits in Mathlib.
4. `msearch.py leansearch`: "Affine-local constructibility of module sheaves on a
   Noetherian scheme is equivalent to a finite global locally closed constructible
   stratification". Eight hits about scheme modules and Noetherian affine-cover
   criteria, no sheaf equivalence.
5. `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for global
   constructibility, affine-local predicates and finite-presentation local models.
   `constructible_etale_module_qcqs_affine_local` has **finite** coefficients and
   is etale-only, so cannot state this item. Global pro-etale predicates likewise
   require finite coefficients. Reused the two already landed affine-local nodes.
6. `rg` for the item id in upstream `WeilConjectures`: no hits. A name search in
   upstream, Mathlib/project sources and `dag/lean_names_upstream.json` found none
   of our four new declaration names. Existing coefficient-sized sites, scalar
   restriction and canonical base-change functors were found and reused, not copied.

No statement dispute or source correction is needed. The additional stmt_deps
are exactly the two already landed affine-local constructibility nodes, and a
read-only graph traversal found no path from either node back to this item.

Validation: `scompile.py NL lem-sfb-noetherian-global-constructibility` compiled
both delivered files separately in dependency order, with exit code 0 and no
warnings. Only the two main theorem proofs are `sorry`; both definitions in the
dependency module have actual data. All variables and universes are explicitly
bound, and no file-local notation, instance, private definition or statement let
is used. Source checks: Stacks 095E, 03RW(3), proetale definition-constructible,
and 005L; finite-type/finite-presentation is the Noetherian coefficient convention.

## Dependency modules

`def-sfb-affine-locally-constructible-proetale-modules`:
`Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules` repairs
only its Lean record, by §1(B). Its original declaration binds `R : Type u` with
`X : Scheme.{u}` and cannot accept an independently sized coefficient ring.
The new module publicly retains that original interface and gives the same
finite affine-local immersed stratification with constructible parts and
finitely presented constant-module models on the already published equivalent
coefficient-sized pro-etale sites. Its thin `coefficientProEtaleFixedModulePullback`
helper specializes the existing actual sheaf-pullback construction to module
coefficients and the existing transported scheme base-change functor.
`IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf` then states the
recorded definition exactly in those coordinates, with the same module values,
covering sieves and restriction maps. No existence choice or strengthened
hypothesis is used. The dependency's statement, stmt_deps and all non-Lean
fields are unchanged; its original module is imported and retained.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
