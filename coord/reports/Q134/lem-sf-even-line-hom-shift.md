## Worker report

The item module `Sheaf.Paper.EvenLineHomShift` defines the actual evaluation
transpose `CategoryTheory.SignedRingedHom.lineComparison` and states
`even_line_hom_shift` and `even_line_hom_shift_normalization`. All postponed
proofs are `by sorry`; the maps, categories, monoidal structures, braiding and
adjunction mates have actual definitions. The dependency repair is described
below. The item statement is unchanged.

Hypotheses and clauses, with the node and both modules open:

* A ringed site small in the module universe is `{C : Type u} [SmallCategory C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{u}`. The module category
  `Modules J R` abbreviates the dependency's actual `SheafOfModules.{u}` for the
  underlying sheaf of rings. A small site and its abelian sheaves retain the
  existing site and module definitions; no geometric hypothesis is introduced.
* `D J R` is the full unbounded `DerivedCategory (Modules J R)`, with
  `[HasDerivedCategory.{u} (Modules J R)]`. The small Hom universe is available
  for every such Grothendieck module category; it is a size choice of the
  localization, not a restriction on its objects. In particular `K : D J R`
  has no perfectness, boundedness, coherence or finiteness assumption.
* The tensor is the upstream derived monoidal structure from total complexes
  and K-flat resolutions. Its associator and unit constraints are the descended
  constraints of complexes; `derivedBraiding` is specifically
  `DerivedMonoidal.braidedCategory`, not a braiding chosen from Nonempty.
  `homFunctor J R` is the recorded `derivedInternalHomOfUniverses` specialized
  to the small module universe, and `hom J R K` fixes its first argument.
* `T : Modules J R` is a sheaf. `hT` says that for every site object a covering
  sieve has slice restrictions of T isomorphic to the restricted ring's unit
  module. This is exactly locally isomorphic to R, including the empty-cover
  cases admitted by J. `(DerivedCategory.singleFunctor (Modules J R) 0).obj T`
  places it in degree zero, and `⟦r⟧` forms T[r]. The native derived tensor unit
  `𝟙_ (D J R)` is the localization of the module unit in degree zero, namely R[0].
* `r s : ℤ` retains negative, zero and positive shifts. `hr : Even r` is precisely
  the only parity restriction. The shifts are Mathlib's cohomological shifts
  (terms i+s and differential (-1)^s).
* `lineComparison J R K B` applies the unique normalized adjunction's homEquiv
  to coefficient evaluation tensored with B. The explicit composite reassociates
  `(H(K,R) tensor B) tensor K`, uses the Koszul braiding of B and K, reassociates
  back, evaluates H(K,R) tensor K to R, and uses the left unitor. Thus both a maps
  in the node are actual transposes, not arbitrary maps with the right endpoints.
* `sourceShift J R K s` is the right-adjoint uniqueness isomorphism for the
  evaluation-normalized adjunctions and the actual tensor shift. Its left-adjoint
  comparison is `X tensor K[s] -> (X tensor K)[s] -> X[s] tensor K`. On the product
  Hom complex, the resulting mate reindexes j=i+s and multiplies degree n by
  (-1)^(s*n), with the usual possible shift-only normalization. This fixes the
  signed map rather than selecting an unspecified natural isomorphism.
* The left side of `even_line_hom_shift` is a_(K[s],T[r]) followed by b_(K,T[r],s).
  The right side is `(b_(K,R,s) ▷ T[r])`, followed by the native `commShiftIso (-s)`
  of tensorRight T[r], followed by `(a_(K,T[r]))⟦-s⟧'`. Lean's `≫` order is the
  source-to-target order, so these are the two sides of the node's displayed
  equality with its required tensor-shift insertion.
* `even_line_hom_shift_normalization` states the same equality with BOTH b maps
  multiplied by `ε : ℤˣ`. These units are exactly the two signs. Since s is fixed
  and ε is arbitrary, this includes every normalization depending only on s.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, with the accompanying
  Grothendieck-topology/sheaf interfaces.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Modules` is only an abbreviation of the same Mathlib module category.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, Q and the cohomological shifts.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses`, its localization construction and representative
  comparisons (the recorded interface of def-pur-derived-internal-hom).
* `Sheaf.Algebra.Homology.HomComplex`: `homComplexFunctor`, `homComplex`,
  `homComplex_exists`, including all product terms and the signed differential.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  the ordinary first/second factor tensor shift comparisons.
* `Sheaf.Algebra.Homology.KFlat`: `IsKFlatIndependentCoefficients` and its
  resolution predicate. `KFlatResolutionIndependentCoefficients` is imported
  as the proof dependency `lem-pc-kflat-resolution`.
* `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`: all three original
  tensor-currying, restriction and exactness statements, retained by public import.
* `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `CoefficientTensorModels`, ordinary total-tensor comparisons, and their fixed
  componentwise evaluation model. Its already-landed definition node is added
  to the item's stmt_deps; no new definition node is introduced.
* Upstream `SheafOfModules.monoidalCategory`, `symmetricCategory`,
  `monoidalClosed`, `isGrothendieckAbelian`; native K-flat derived monoidal
  and shift instances; `Adjunction.rightAdjointUniq` and `shiftEquiv`.

Searches made:

* msearch leanfinder: “The internal derived Hom tensor comparison for an even
  shifted line sheaf commutes with shifting the first Hom argument”: eight hits,
  principally exact-functor shift facts and ShiftedHom, none the asserted square.
* msearch loogle `internalHom, shift`: no match (unknown unqualified internalHom).
* msearch grep `internalHom.*shift|ihom.*shift|shift.*ihom|shift.*internalHom`:
  no Mathlib hits.
* msearch leansearch “Derived internal Hom tensor line even shift compatibility
  cochain complex signs”: eight hits, including HomComplex.Cochain.leftShift_v,
  leftUnshift_v and their linear equivalences. These are ordinary cochains, not
  the module-sheaf derived evaluation square.
* rg of upstream WeilConjectures and side lean/Sheaf for line/Hom/shift,
  evaluation, transpose, derivedTensor shift, the proposed names and the item id:
  no exact statement. Found and read the recorded Hom shift existence theorems,
  the native derived monoidal API and the coefficient representative model.
* `tools/blueprint_refs.py search 'tensor Hom shift'`: zero blueprint matches.
  The existing item and dependencies already carry the notions needed.
* Read `dag/lean_names_upstream.json`, Mathlib HomComplexShift and BifunctorShift,
  the recorded dependency source/docstrings, the current server source of
  RingedInternalHomExactRestriction, Stacks sections 0A8X/08J7 and Tags
  08J9/08JB/08JC, and current blueprint thm-sf-dual-perfect proof Step 4.

Edge cases checked: empty site and covering sieve; zero sheaves/complexes;
zero coefficient ring; r=0, s=0; negative even r and negative s; arbitrary
unbounded K; both signs ε=+1 and ε=-1. The sign ratio is 1 whenever r is even,
including negative even r. The construction of b uses only the fixed shift
and adjunction and introduces no K-flatness condition on K itself. For s=0
it is the identity comparison under the unit shift identifications.

## Dependency modules

`lem-weil-pbc-ringed-internal-hom-exact-restriction` is repaired under §1(B)
in `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`. Its old interface
only asserts existence of currying and of CommShift structures; it cannot
name the prescribed evaluation transpose or the prescribed signed b map.
A bare choice from the old Nonempty shift result would not fix its sign or
its representative compatibility. All old declarations remain available by
public import, so the restriction and triangle assertions are preserved.

The repair supplies the actual ordinary monoidal tensor on this module
category and its derived category; auxiliary additivity and functorial local
free-cover facts state the infrastructure used by that construction. The
closed adjunction is selected from a named uniqueness theorem, normalized
both on the actual Hom/K-injective representatives and against the native
localization tensor map. Thus the theorem fixes the data used downstream;
it is not a choice of arbitrary maps from a mere existence statement.
`sourceShift` is its actual adjunction mate under ordinary tensor shifts.
Every auxiliary theorem is named, has the owning dependency's blueprint tag,
and explains the construction step it supplies. No live library file was edited.

## Second reading by Q134

Author's final self-check, not an independent review: compared every binder,
map and clause against the node as listed above. The original independent
maintainer review remains required by the dispatch brief. Checked the direction
of both mates, the `≫` order, the explicit tensor shift, the ordinary degree-zero
line, and use of the recorded H rather than a copied Hom construction. During
this check the representative comparison was fixed to the native localization
map as well as evaluation, eliminating a possible rescaling ambiguity in the
adjunction uniqueness statement. No item statement correction was needed.

The interface additionally names the equality between the native monoidal
instance and its explicit localization implementation, and between the two
ordinary total-tensor implementations. These equalities supply explicit
transports instead of repeatedly unfolding large instance expressions. Their
proofs are postponed with the same owning dependency; their data are fixed
existing constructions, never unspecified replacements. The normalization
in `normalizedAdjunction_existsUnique` fixes the entire closed structure S,
with `S.monoidal` equal to the native tensor and its model comparison inverse
to the native localization tensor map (after the explicit total-tensor
identification). This fixes the adjunction as well as its representative maps.

Validation: `scompile.py Q134 lem-sf-even-line-hom-shift` compiled both delivered
modules, including each sandbox import and library path, with exit code 0 and
no unexpected warnings. The final library-path compiles took 32.0 seconds for
SignedCalculus and 28.5 seconds for EvenLineHomShift, within the fixed limit.

The first delivery dry run compiled both files, then flagged imported legacy
declarations in `lean.declarations`. The record now lists only declarations
owned by SignedCalculus; the public import continues to preserve all legacy
restriction, exactness and currying declarations. No Lean change was needed.
