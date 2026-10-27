## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceModuleIsomAffine` states
`AlgebraicGeometry.AlgebraicSpace.module_isom_affine`, with a single `sorry` proof.
It represents the relative module Isom functor by an algebraic space affine and of
finite presentation over B. There are no new definitions, dependency repairs, or
statement corrections. Source read: `literature/stacks-project/quot.tex`, Situation
08JT (`situation-hom`, lines 182–201) and Proposition 08K9 (`proposition-isom`,
lines 820–863), including the preceding definition of the Isom functor.

Hypothesis and conclusion correspondence:

- A scheme S, with the size convention: explicit `universe u`, `{S : Scheme.{u}}`.
  Both spaces are `{X B : AlgebraicSpace S}`. All scheme tests use the same universe
  as S, and module sections use the existing small-etale module categories.
- A morphism of algebraic spaces: `(f : X ⟶ B)`.
- Finite presentation of f: `hf : ProperQuotFinitePresentation f`. Its existing
  definition is exactly local finite presentation, `MapIsQuasiCompact f.hom.hom`,
  and quasi-compactness of `Limits.pullback.diagonal f.hom.hom`.
- Quasi-coherent modules on the small etale ringed site: `(M N : X.QCoh)`.
  `QCoh` is the existing full subcategory for Mathlib's `IsQuasicoherent` predicate.
- Finite presentation of each module: `hMfp : M.obj.IsFinitePresentation` and
  `hNfp : N.obj.IsFinitePresentation`. Mathlib's predicate is a local cokernel
  presentation by finite free sheaves, exactly the stated convention.
- Relative flatness of both modules: `hMflat : ModuleIsFlatOver f M.obj` and its
  N analogue. The existing predicate quantifies over every compatible pair of
  etale scheme charts and uses `Scheme.Modules.IsFlatOver` on the Zariski restriction.
  For quasi-coherent modules this is the specified stalkwise condition. The already
  landed owning node `def-sfb-space-flat-proper-coefficient` is added to stmt_deps,
  as permitted for an existing recorded definition. Its annihilator-support
  predicate is deliberately not used: the item specifies the proper-carrier form.
- Proper support of M: `hMsupport` quantifies over an actual algebraic space Z and
  `i : Z ⟶ X`, requires `IsRepresentableWith` closed scheme immersions,
  `MapIsProper (i ≫ f)`, and an E with `E.IsQuasicoherent`, `E.IsFiniteType`, and
  `Nonempty ((moduleDirectImage i).obj E ≅ M.obj)`. `hNsupport` gives every same
  clause for N. This spells out the carrier definition from the Quot dependency;
  no annihilator ideal or finiteness of f beyond finite presentation is assumed.
- Every scheme T over B: `T : ProperQuotTest B`, the existing
  `CostructuredArrow yoneda B.obj.obj`. T.left is its S-scheme and T.hom its map to B.
- The specified X_T and module base changes: `properQuotFibre f T`, its projection
  `properQuotFst f T`, and `(moduleTensorPullback (properQuotFst f T)).obj M.obj`
  and the identical expression with N. These are the existing actual sheaf pullbacks.
- An algebraic space I over B: `∃ (I : AlgebraicSpace S) (p : I ⟶ B)`.
- Affine over B: `IsRepresentableWith (fun _ _ q ↦ IsAffineHom q.left) p.hom.hom`.
  It supplies representing scheme pullbacks which are affine morphisms; equivalently
  every pullback to an affine scheme over B is an affine scheme. It does not require
  B itself to be a scheme or affine.
- Finite presentation of p, including quasi-compactness and quasi-separatedness:
  `ProperQuotFinitePresentation p`, the same three-part predicate used for f.
- Representing bijections on every T: the existential family `e` is an Equiv from
  `{g : yoneda.obj T.left ⟶ I.obj.obj // g ≫ p.hom.hom = T.hom}` to the actual
  type of isomorphisms between the two tensor pullbacks. The subtype is exactly
  maps over B from T to I, by the full embeddings and Yoneda.
- Naturality for EVERY scheme morphism T' → T over B: the final universal clause
  quantifies over h, g and g' with `g'.val = yoneda.map h.left ≫ g.val`. Such a g'
  always exists: h's costructured-arrow triangle and g.property prove its subtype
  condition. Thus the implication loses no tests and avoids a separate proof helper.
  Its conclusion identifies `e T' g'` with pullback of `e T g` conjugated by
  `properQuotSourceIso f M.obj h` and `properQuotSourceIso f N.obj h`.
  The source comparison is used inversely and the target comparison forwards,
  giving exactly M_T' → N_T'. These comparisons use the already tensor-normalized
  `moduleTensorComposition`, rather than arbitrary isomorphisms.
- No assumption makes f flat, proper or separated; B need not be Noetherian.

Dependency declarations used (source signatures and docstrings read):

| Module | Declarations |
| --- | --- |
| `Mathlib.AlgebraicGeometry.Scheme` | `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpace` | `AlgebraicSpace`, `IsRepresentableWith`, `Modules`, `EtaleSite`, `moduleTensorPullback`'s underlying ringed sites |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` | `MapIsLocallyOfFinitePresentation`, `MapIsProper` |
| `Sheaf.AlgebraicGeometry.ProperCurveModuli` | `MapIsQuasiCompact` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` | `fibreProduct_isAlgebraicSpace`, used by the fibre definition |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` | `QCoh` |
| `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` | `SheafOfModules.IsQuasicoherent`, `SheafOfModules.IsFinitePresentation` |
| `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` | `SheafOfModules.IsFiniteType` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations` | `moduleTensorPullback`, `moduleDirectImage` |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` | `Scheme.Modules.IsFlatOver` through `ModuleIsFlatOver` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction` | `schemeRestriction` through `ModuleIsFlatOver` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient` | `ModuleIsFlatOver` |
| `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor` | `ProperQuotFinitePresentation`, `ProperQuotTest`, `properQuotFst`, `properQuotFibreMap`, `properQuotSourceIso` |
| `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange` | `moduleTensorComposition` through `properQuotSourceIso` |
| `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` | `IsClosedImmersion` |
| `Mathlib.AlgebraicGeometry.Morphisms.Affine` | `IsAffineHom` |

The size-convention node is metatheoretic: its recorded declaration is null and its
universes are rendered explicitly. The two separately imported recorded proof modules
are `AlgebraicSpaceFlatProperFpLocality` (`flat_proper_fp_locality`) and
`AlgebraicSpaceRepresentableEtaleSchemeTests` (`representable_etale_scheme_tests`).
The other recorded proof modules already occur as public statement imports through
SpaceProperQuotFunctor. The proof-only nodes `lem-sfb-space-module-hom-affine`,
`lem-sfb-space-affine-locality`, `lem-sfb-space-separated-fp-composition`, and
`lem-sfb-space-relative-lfp-permanence` have no recorded Lean declaration at inspection;
there is no module for them to import. They are only postponed proof inputs, not
missing notions needed to state this theorem. The docstring retains every proof step.

Edge cases checked before writing: both modules zero (Isom is the singleton functor,
represented by B); one module zero (the fibre is empty precisely where the other
fails to vanish, with no nonzero assumption); empty X (the unique module isomorphism,
again represented by B); empty B and empty scheme tests (the formulation still has the
unique empty-base fibre); non-affine and non-schematic B; non-Noetherian bases; and
identity and arbitrary, possibly nonflat, transition maps. No rank, characteristic,
nonemptiness or equality of unrelated universe levels is imposed. No statement dispute
or correction was needed.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “Isomorphisms of finitely presented flat quasi coherent
  modules with proper support represented by an affine algebraic space of finite
  presentation”. Eight results: Mathlib module-presentation data, affine-space finite
  presentation, and flat scheme maps; none represents this Isom functor.
- `msearch.py ... loogle '"Isom", "AlgebraicGeometry"'`: twelve results, concerning
  ringed-space isomorphism constructors and scheme isomorphism properties; no match.
- `msearch.py ... leansearch`: “The Isom functor between flat finitely presented quasi
  coherent modules with proper support is affine of finite presentation”. Eight results,
  including FG-module equivalences, scheme isomorphism criteria and descent; no match.
- `msearch.py ... grep 'IsomFunctor|isomFunctor|Isom.*represent|isom.*affine'
  AlgebraicGeometry`: eight affine-scheme/affine-morphism and scheme-isomorphism hits;
  no relative module Isom representability theorem.
- `rg -n 'IsomFunctor|isomFunctor|module_isom_affine|moduleIsom|ModuleIsom|lem-sfb-space-module-isom-affine'
  lean/WeilConjectures lean/Sheaf`: only unrelated formal-module and constant-module
  isomorphism module imports. No existing declaration for this item.
- `rg` in `dag/lean_names_upstream.json` for the new theorem name and reused predicate
  names: no upstream declaration collision. Searches of existing algebraic-space
  modules found the reusable Quot interfaces and `ModuleIsFlatOver`, both used directly.

Validation: `scompile.py NP lem-sfb-space-module-isom-affine <module path>` passed in
both sandbox mode (2.8 seconds) and library-module mode (2.3 seconds), with no errors
or unexpected warnings. All binders are explicit and both auto-implicit modes are off.

## Second reading by NP

A separate second pass by this worker opened the node and completed module together.
No second agent was started, as the dispatch brief prohibits it; the maintainer supplies
independent review. The pass checked the exact source hypotheses against the eight
binders f/hf/M/N/finite-presentation/flatness/two support witnesses, then checked
both output morphism properties and every scheme-test equivalence. In particular,
the support witnesses retain finite type AND quasi-coherence of E, finite presentation
of p retains its diagonal condition, and the naturality equation has the source inverse
and target forward comparison in the correct order. The g' premise is always realizable
and thus imposes no restriction on h or g. Empty and zero cases introduce no extra
assumptions. The owning node for the reused relative-flatness predicate was added to
stmt_deps. No mathematical mismatch or statement correction was found.
