## Worker report

Retained the saved packet, read its report, and started with the prescribed
`deliver2.py Q110 sk-def-cd --no-push`. The current delivery contains one module,
`Sheaf.AlgebraicGeometry.CohomologicalDimension`, and changes only the item's `lean`
record. The natural statement, dependencies and proof plan are unchanged. No new
nodes or dependency modules are needed. There is no statement dispute.

Clause-by-clause correspondence:

- The fixed prime is `(ℓ : ℕ) (hℓ : Nat.Prime ℓ)`. Coefficients are
  `AddCommGrpCat.{u + 1}` sheaves on `Scheme.ProEt.topology X` or
  `X.smallEtaleTopology`; no invertibility or characteristic assumption is imposed.
- `ellPowerKernel ℓ r` is `kernel ((ℓ ^ r : ℕ) • 𝟙 F)`, including `r = 0`.
  `ellPowerKernelMap` is the canonical kernel lift for `r ≤ s`.
  `ellPowerKernelFunctor : ℕ ⥤ A` records these inclusions;
  `ellPowerKernelCocone` has apex F and the kernel inclusions, and
  `ellPowerKernelColimitMap` is exactly its `colimit.desc`. These helpers are
  generic in an abelian category, so the SAME construction applies on both sites.
- `IsEllPowerTorsion ℓ hℓ F` means `IsIso` of this canonical map on EITHER site.
  `IsEllPowerTorsionLocal` and `isEllPowerTorsion_iff_local` additionally express
  the local sectionwise criterion on the pro-étale site: every section admits a
  covering sieve on whose arrows the restricted section is killed by some power.
  The exponent is allowed to depend on the section and covering arrow.
- Classical abelian sheaves use `IsClassicalAbelian F`, applying the RECORDED
  `AlgebraicGeometry.ProEtale.IsClassical` to the underlying set sheaf through
  `sheafCompose ... (forget AddCommGrpCat)`. No private classicality criterion is used.
- The qcqs scheme hypothesis is `[CompactSpace X] [QuasiSeparatedSpace X]` on
  `cohomologicalDimension` and its absolute comparison. The qcqs morphism
  hypothesis is `[QuasiCompact g] [QuasiSeparated g]` on
  `relativeCohomologicalDimension` and its relative comparison.
- Each supremum is `sSup` of a subset of `WithTop ℕ`, formed from degrees
  `n : ℕ` with `q = n` and an existential classical prime-power torsion sheaf.
  Thus negative degrees and top itself are not candidate degrees; an unbounded
  set has supremum top, and the empty supremum is bottom, namely 0.
- `IsNonzeroProEtaleCohomology F n` is `¬ IsZero` of degree-n homology of
  `ProEtale.rightDerivedGlobalSections AddCommGrpCat X` applied to
  `DerivedCategory.singleFunctor _ 0`. This is precisely the node's H^n(RΓ(F)).
  It now uses the node's derived-global-sections object directly.
- `IsNonzeroProEtaleHigherDirectImage g F n` is `¬ IsZero` of degree-n
  homology of `(ProEtale.lowerStar AddCommGrpCat g).rightDerivedFunctor`
  on the same degree-zero single. The recorded pushforward is precomposition
  with base change, so this is R^n g_* F.
- For a field, the notation cd_ℓ(K) is the expression
  `cohomologicalDimension ℓ hℓ (Spec (.of K))`; no second invariant is introduced.
- `etaleCohomologicalDimension` uses the SAME canonical torsion predicate and
  `Etale.cohomology` on the degree-zero single. The two comparison theorems
  identify the absolute and relative suprema with their usual étale formulas,
  under respectively the scheme and morphism qcqs assumptions.
- BOTH finite-type finiteness theorems retain `[Field K]` and
  `hK : cohomologicalDimension ℓ hℓ (Spec (.of K)) < ⊤`.
  A scheme over K is `[X.Over (Spec (.of K))]`; finite type is
  `[LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]`.
  The relative theorem has these hypotheses for X and Y, and also
  `[g.IsOver (Spec (.of K))] [LocallyOfFiniteType g] [QuasiCompact g]`.
  The explicit proofs passed to the dimension definitions derive the remaining
  qcqs properties from finite type over a field, using the existing Mathlib
  `LocallyOfFiniteType.isLocallyNoetherian`,
  `IsLocallyNoetherian.quasiSeparatedSpace`, and
  `QuasiCompact.compactSpace_of_compactSpace`. No separatedness assumption is added.

Dependency declarations inspected and used:

- `sk-def-pe-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology` in `Mathlib.AlgebraicGeometry.Sites.Proetale`.
  This is the weakly étale small site with the finite-refinement fpqc topology.
- `sk-def-pe-classical-definition`: `AlgebraicGeometry.ProEtale.IsClassical`,
  `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`, exact affine-presentation
  continuity-map bijectivity on underlying sets. The saved dependency copy is
  removed: Q18 has already landed its exact existing record.
- `def-weil-pbc-scheme-conventions`: the recorded convention node defines no
  extra object; its referenced Mathlib classes `QuasiCompact`, `QuasiSeparated`
  and `LocallyOfFiniteType` are used, with the underlying scheme's topological
  compactness and quasi-separatedness for the absolute invariant.
- `def-pur-abelian-sheaf-kernel`: `CategoryTheory.Limits.kernel`,
  `kernel.ι`, `kernel.lift`, in the recorded abelian sheaf category
  (`CategoryTheory.sheafIsAbelian`).
- `def-weil-pbc-category-colimit`: `Cocone`, `colimit`, `colimit.desc`,
  `Mathlib.CategoryTheory.Limits.HasLimits`.
- `det-pe-topos-functoriality-inverse-image`: recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage` is imported;
  its underlying direct image is the existing `ProEtale.lowerStar` from
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
- `def-sfb-right-derived-functor`: recorded module
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` is imported.
  The actual sheaf categories have `HasKInjectiveResolutions`, so their
  pushforwards and global sections use the existing upstream
  `CategoryTheory.Functor.rightDerivedFunctor` special case. It has the same
  universal right-derived property and is computed on K-injective resolutions;
  no new derived functor or resolution hypothesis is introduced here.
- `def-weil-pbc-etale-cohomology`: `AlgebraicGeometry.Etale.cohomology`,
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, followed by the
  generic total derived functor and `DerivedCategory.homologyFunctor`.
- `def-weil-scheme-over-base`: `Scheme.Over`, `Scheme.Hom.IsOver` and
  the structure map `↘`, `Mathlib.AlgebraicGeometry.Over`.

All stated proof dependencies have their available modules imported except the
following two. `sk-thm-pe-direct-image-comparison` has no recorded declaration yet.
`sk-prop-sf-comparison` is recorded in `BoundedBelowProEtaleComparison`, but adding
that module makes its overlay fail with the duplicate
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, from the
upstream generic and finite-coefficient lower-shriek files. Following the required
smaller-import repair, the delivery imports upstream
`WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` instead. Recompilation
succeeds. This omission affects the stage-3 proof-import plan only, not a statement
object or hypothesis. Other proof imports are retained for the node's six-step plan.

Edge cases: r = 0 is the kernel of the identity; exponents may vary locally;
zero sheaves and empty schemes contribute no nonzero degrees; q = 0 is included;
identity morphisms remain permitted; empty sources remain permitted; unbounded
sets of nonzero degrees give top; arbitrary characteristic and ℓ equal to the
characteristic remain allowed. Neither identity-morphism quasi-compactness nor
identity-morphism quasi-separatedness is substituted for a qcqs scheme.

Searches retained from the saved investigation and stage-1 search record:
`msearch.py` LeanFinder for prime-power pro-étale cohomological dimension found
only injective/projective-dimension results; Loogle `"cohomologicalDimension"`
returned no match; Mathlib grep `cohomologicalDimension|cohomological.dimension|ProEtale`
found topology and individual cohomology declarations, not this invariant;
LeanSearch `ell primary torsion etale cohomological dimension of a scheme`
found étale-topology and algebra results only. The saved source grep for
`classical.*sheaf|IsClassical|etaleOrigin` located classicality sources.
Current source grep for `ellPowerKernel|IsEllPowerTorsion|(^| )cohomologicalDimension|relativeCohomologicalDimension`
in `WeilConjectures/` and `lean/Sheaf/` has no hits. Existing generic kernels,
colimits, derived functors and the recorded classicality definition are reused.
Read the current blueprint unit and the local Stacks source for Tag 0F10.

Self-check repairs to the saved packet: restored the actual qcqs hypotheses on
both dimension definitions; replaced the tautological identity-morphism
hypotheses on the absolute comparison by `CompactSpace` and
`QuasiSeparatedSpace`; rendered nonvanishing directly on the specified derived
cohomology objects; added the field finiteness hypothesis and K-morphism condition
to relative finiteness; removed independent quasi-separatedness assumptions from
the finite-type clauses by supplying the existing derived evidence; shared the
canonical torsion construction on both sites; completed source/proof docstrings;
removed the already-landed dependency record and the earlier self-written
second-reading section. The separate second reader remains responsible for the
independent reading.

All postponed obligations are named theorems owned by this node and listed in
`lean.declarations`: the scalar annihilation identity, the diagram identity and
composition laws, cocone naturality, the local-torsion equivalence, two comparison
clauses and two finiteness clauses. Each has a natural-language proof docstring;
all proofs are `sorry`. Definitions have real constructions. The final validation
is the prescribed per-file `scompile.py` and `deliver2.py --no-push` dry run.

Final `scompile.py` validation of the complete module: exit 0, no errors or
warnings; sandbox compile 3.0 s and library-path compile 3.1 s.

The required first dry run reported four preflight findings on the initial saved
metadata: a removed `IsEllPowerTorsionEtale` declaration, the old absolute
signature, the stale dependency copy without a dependency-report section, and
the missing independent second reading. The first three are repaired by the
final declaration inventory/signature and removal of the independently landed
dependency copy. The fourth is intentionally reserved for the separate reader;
the dry-run tool explicitly permits that sole outstanding reader requirement.


## Second reading by Q110

I read the item JSON and its original blueprint unit (`sk-def-cd/_section.md`,
order 1506), the local Stacks source for Tag 0F10
(`etale-cohomology.tex`, `lemma-finite-cd`, with `definition-cd` and
`definition-cd-f`), pro-étale comparison Tags 099V, 099W and 09A6
(`proetale.tex`, the relative/cohomology/morphism comparison lemmas), every
statement dependency record, and the declarations
below. The source assumes a field in the finiteness clause; it imposes no
invertibility, characteristic, separatedness, or uniform torsion-exponent
assumption. The node already makes the local torsion convention and the
fixed-prime absolute finiteness argument precise. It has no `statement_change`;
no correction of the node or its unit is required. There is no repair-note file
for this item, no new definition node, and no dependency module in this packet.

My object/hypothesis/conclusion checklist, independently matched to the file:

1. **Fixed prime and coefficients.** `ℓ : ℕ`, `hℓ : Nat.Prime ℓ`, and
   `Sheaf ... AddCommGrpCat.{u + 1}` give precisely a prime and abelian sheaves.
   Verdict: exact; no coefficient ring or invertibility hypothesis is introduced.
2. **Annihilator objects and inclusions.** `ellPowerKernel ℓ r` is the actual
   categorical kernel of `(ℓ ^ r : ℕ) • 𝟙 F`. `ellPowerKernelMap ℓ h` is its
   kernel lift with the smaller kernel inclusion as underlying arrow, for
   `h : r ≤ s`. The named annihilation lemma and diagram-law lemmas only supply
   the proof fields for this canonical construction. Verdict: the diagram is
   the specified increasing kernel diagram, rather than arbitrary maps.
3. **Local prime-power torsion on either site.** `ellPowerKernelCocone` has apex
   `F` and kernel inclusions; `ellPowerKernelColimitMap` is `colimit.desc` of
   that cocone. `IsEllPowerTorsion` is `IsIso` of exactly that map. These helpers
   are generic in an abelian category, and both sites use that same predicate.
   `IsEllPowerTorsionLocal` permits a covering sieve and an exponent for each
   restriction of each section; `isEllPowerTorsion_iff_local` states its
   equivalence to the canonical definition. Verdict: exact local torsion,
   with no common exponent and no demand on all sections before localization.
4. **Small pro-étale site and classicality.** Both suprema use
   `Scheme.ProEt.topology X`. `IsClassicalAbelian` applies the dependency's
   `ProEtale.IsClassical` to the underlying set sheaf via `sheafCompose` and
   `forget AddCommGrpCat`; it introduces no alternate continuity criterion.
   Verdict: the node's small weakly étale site and classical sheaves.
5. **Absolute object and qcqs hypothesis.**
   `cohomologicalDimension ℓ hℓ X [CompactSpace X] [QuasiSeparatedSpace X]`
   is the absolute invariant for a qcqs scheme. Its set has
   `∃ n : ℕ, q = n ∧ ∃ F, IsClassicalAbelian F ∧ IsEllPowerTorsion ... F ∧ ...`.
   `IsNonzeroProEtaleCohomology F n` is the negation of `IsZero` for degree-n
   homology of `rightDerivedGlobalSections ... X` on `singleFunctor _ 0 F`.
   Verdict: precisely the first displayed supremum and its derived notation.
6. **Relative object and qcqs hypothesis.**
   `relativeCohomologicalDimension ℓ hℓ g [QuasiCompact g] [QuasiSeparated g]`
   uses sheaves on X, with the same quantifier order and coefficient conditions.
   `IsNonzeroProEtaleHigherDirectImage` takes homology of
   `(ProEtale.lowerStar ... g).rightDerivedFunctor` on a degree-zero sheaf.
   Verdict: precisely the second displayed supremum; neither X nor Y is
   separately required to be qcqs.
7. **Degrees, infinity and field notation.** Both values lie in `WithTop ℕ`,
   with candidate degrees exactly the embedded `n : ℕ`. Thus degree zero is
   included, negative degrees and infinity are not candidates, an unbounded
   set has supremum infinity, and the empty supremum is zero. Field dimension
   is the expression `cohomologicalDimension ℓ hℓ (Spec (.of K))`, also used
   literally in the finiteness hypotheses. Verdict: exact; the field notation
   denotes this existing expression and creates no second invariant.
8. **Absolute comparison.** `etaleCohomologicalDimension` uses the same
   kernel-colimit torsion predicate on étale abelian sheaves, without a
   classicality restriction. Its nonzero object is the recorded
   `Etale.cohomology ... X (n : ℤ)` on `singleFunctor _ 0 F`.
   `cohomologicalDimension_eq_etaleCohomologicalDimension` asserts equality
   under exactly the qcqs scheme hypotheses. Verdict: all of the absolute
   comparison clause.
9. **Relative comparison.** `relativeCohomologicalDimension_eq_etale` asserts
   equality with the analogous étale supremum, using `Etale.lowerStar` and its
   total right derived functor, under exactly qcqs g. Verdict: all of the
   relative comparison clause, without assuming qcqs bases.
10. **Relative finite-type finiteness.**
    `relativeCohomologicalDimension_lt_top_of_finiteType` retains `[Field K]`,
    finite field dimension `hK`, finite-type X and Y over `Spec K`, a morphism
    `g` with `[g.IsOver (Spec (.of K))]`, and finite type g. Locally finite
    type plus quasi-compact is precisely the recorded finite-type convention.
    The conclusion is the relative dimension `< ⊤`; its quasi-separatedness
    instance is supplied from the Noetherian source, rather than assumed.
    Verdict: the relative finiteness assertion with every stated hypothesis.
11. **Absolute finite-type finiteness.**
    `cohomologicalDimension_lt_top_of_finiteType` has the same field and `hK`
    assumptions and precisely a finite-type K-scheme X. Its conclusion `< ⊤`
    supplies both qcqs instances from finite type over the field. Verdict:
    the absolute finiteness assertion, without a separatedness assumption or
    strengthening to finite all-torsion dimension of K.

Dependency/interface checks: I opened `ClassicalContinuityMap.lean`, including
`AffinePresentation`, `continuityMap`, and `IsClassical` (all affine étale
presentations and the actual restriction-induced colimit map); the recorded
`ProEtaleToposFunctorialityInverseImage.lean`; and
`RightDerivedFunctorOfQuasiIsoResolutions.lean`. I read `Scheme.ProEt` and its
`topology` in pinned Mathlib, `kernel`/`kernel.lift`, and the chosen-colimit
interface. `Scheme.ProEt` uses weakly étale objects and the fpqc
finite-refinement topology, without a globally finite covering requirement.
I also read `coord/pefw-upstream-framework.md` and the actual generic
`lowerStar`/`rightDerivedGlobalSections` source in the shared `lean/WeilConjectures`
tree. The former is restriction along base change and the latter is the total
right derived of `Sheaf.Γ`. The pinned étale `lowerStar` and `Etale.cohomology`
source has the matching objects and degrees. The upstream
`Functor.rightDerivedFunctor` is literally `totalRightDerived` of the degreewise
homotopy-category functor; its K-injective-resolution requirement is available
for these sheaf categories and is not an extra binder in any statement here.
Consequently it specializes the dependency's general universal right-derived
notion, rather than replacing that notion. The scheme convention record
introduces no new object; the used Mathlib properties match it.

Edge cases: the fixed exponent index is the nonempty directed category ℕ,
including r = 0, where the kernel is the kernel of the identity. Local exponents
may vary across arbitrarily disconnected covers. Zero sheaves contribute no
nonvanishing degree; empty schemes and morphisms with empty source are allowed
and yield the empty degree set and dimension zero. Degree n = 0, identity
morphisms, arbitrary characteristic, and ℓ equal to the characteristic are all
allowed. No independent Noetherian or separatedness binder occurs. All schemes
are `Scheme.{u}`, both coefficient categories are `AddCommGrpCat.{u + 1}` as in
the recorded cohomology interfaces, and the actual small-site object and morphism
universes are retained; there is no equality imposed between them. Generic
kernel helpers have separately bound category object/morphism universes v,w.
`autoImplicit false` and the successful compile confirm no unbound variables.

Independent H4 searches (using different queries from the worker):

- `msearch.py ... leanfinder "prime-power torsion cohomological dimension of a
  scheme or morphism"`: eight hits, all injective/projective dimension bounds;
  none defines a site/scheme supremum over classical primary torsion sheaves.
- `msearch.py ... leansearch "A sheaf is primary torsion if it is the union of
  the kernels of multiplication by powers of a prime"`: module torsion results
  such as `Submodule.isTorsion'_powers_iff`, finite primary decomposition, and
  finite-type module sheaves. I checked their reported types: sectionwise
  torsion for a module is not the local sheaf-colimit condition here.
- `msearch.py ... loogle '"ellPowerKernel"'`: no hit.
- `msearch.py ... grep
  'cohomologicalDimension|IsEllPowerTorsion|CohomologicalDimension'`: no Mathlib
  hit. The initially attempted subdirectory prefix `Mathlib/AlgebraicGeometry`
  was only a directory-filtered query; the direct source searches below supply
  the full independent grep check.
- Direct `rg` searches of pinned Mathlib, upstream `WeilConjectures/`, and
  project `lean/Sheaf/` with `prime.?power|primary.?torsion|torsionBy` and the
  invariant's names found module annihilators/decompositions, numerical
  all-torsion étale dimension, and full/uniform derived-amplitude bounds.
  I opened `Sites/TorsionEtaleCohomologicalDimension.lean` and
  `Sites/CohomologicalDimension.lean`: their coefficients are ALL torsion
  sheaves. They do not define this fixed-prime invariant. The upstream uniform
  predicates likewise quantify a different coefficient class. Existing kernels,
  colimits, classicality, direct images and derived functors are reused.

Mismatches and repairs: I found no mathematical mismatch requiring a signature
or node correction. Several helper-definition docstrings had a blueprint marker
without an explicit source place; I added the opening convention or the relevant
displayed formula. I documented the field notation in the absolute definition's
docstring. I expanded the relative finiteness proof plan with the local
prime-power-to-torsion step and the Noetherian-source argument for the diagonal;
I made the corresponding qcqs check explicit in absolute finiteness. The worker's
correct constructions, signatures, hypotheses, node statement, and `lean`
record were retained. No data definition contains `sorry`; all postponed proof
obligations are named, docstringed theorems listed in `lean.declarations`.
The only tactic terms inside definitions merely assemble the specified cocone
from the named naturality theorem. All theorem proofs remain `sorry`.

Validation: the initial independent `scompile.py` compiled both the sandbox and
library-path versions cleanly (3.2 s each). The final source is recompiled below
through the same prescribed wrapper: both versions again passed without errors or
warnings (3.2 s sandbox, 3.4 s library path). The stored primary signature is
verbatim present in the source; all lines are at most 100 characters, the nine
theorems have exactly nine `sorry` proofs, and only the node's `lean` field differs
from the shared node. Delivery is gated by a successful `deliver2.py --no-push`;
no direct build or preflight command is used.

Final dry run: `deliver2.py Q110 sk-def-cd --no-push` printed
`OK (dry run): commit e6dd47b029 passes the preflight and compiles; nothing pushed`.
